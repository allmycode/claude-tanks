// Логика игры «Танки». Общая для браузера (одиночная игра) и сервера (сетевая игра).
// Не трогает DOM: звуки и визуальные эффекты отдаются наружу через emit(...).
(function (root) {
'use strict';

const CELL = 6, N = 104, FS = CELL * N, TS = 48;        // клетка, клеток по стороне, размер поля, размер танка
const LC = 12, LN = 52;                                  // клетка и размер сетки разметки уровня
const EMPTY = 0, BRICK = 1, STEEL = 2, WATER = 3, BUSH = 4, ICE = 5, BASE = 6;
const STAGES = (typeof module !== 'undefined' && module.exports ? require('./stages.js') : root.TanksStages) || [];
const BOT_TYPES = { basic: 0, fast: 1, power: 2, armor: 3 };
const ICE_SLIDE = 0.3;                                   // сколько секунд игрок скользит по льду после отпускания
const DX = [0, 1, 0, -1], DY = [-1, 0, 1, 0];          // 0 вверх, 1 вправо, 2 вниз, 3 влево
const BASE_X = 288, BASE_Y = 576;
const SPAWNS = [0, 288, 576];
const STUN_TIME = 3;
// Попадание в гусеницу обездвиживает танк вместо поражения. Пока выключено:
// любое попадание поражает танк, как в оригинальной игре.
const TRACK_HITS = false;
const ETYPES = [
  { speed: 48,  bspeed: 260, hp: 1, score: 100 }, // обычный
  { speed: 100, bspeed: 300, hp: 1, score: 200 }, // быстрый
  { speed: 58,  bspeed: 450, hp: 1, score: 300 }, // скорострельный
  { speed: 46,  bspeed: 300, hp: 4, score: 400 }, // броневик
];
// Бонусы и их веса при выпадении: звезда выпадает вдвое чаще остальных (2 из 7, около 29%)
const PU_WEIGHTS = { helmet: 1, star: 2, grenade: 1, clock: 1, shovel: 1, tank: 1 };
const EXTRA_LIFE_SCORE = 20000;                          // разовая дополнительная жизнь, как в оригинале
const PARTNER_FREEZE = 3;                                // сколько секунд стоит танк, подбитый напарником
const DONE_TIME = 8, TALLY_DELAY = 1.5;                  // длительность фазы «уровень пройден» и пауза до табло
const TALLY_BONUS = 1000;                                // при игре вдвоём — тому, кто уничтожил больше врагов

function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
const rand = (a, b) => a + Math.random() * (b - a);
const rectsOverlap = (ax, ay, aw, ah, bx, by, bw, bh) => ax < bx + bw && ax + aw > bx && ay < by + bh && ay + ah > by;
const gi = (c, r) => r * N + c;

// opts.emit(type, ...args) — события для звука и эффектов;
// opts.trackChanges — копить изменения карты в G.changes (для сервера)
function createGame(opts = {}) {
  const emit = opts.emit || function () {};
  const track = !!opts.trackChanges;
  const G = {
    state: 'intro', stateT: 0, level: 1, twoP: false, paused: false,
    players: [], enemies: [], bullets: [], powerups: [], stars: [], queue: [],
    spawnTimer: 0, spawnIdx: 0, nextId: 0, freeze: 0, shovel: 0, baseAlive: true, stageTime: 0, tallyBonus: -1,
    grid: new Uint8Array(N * N), gridVer: 0, fullGrid: true, changes: [],
    inputs: [{ dir: -1, fire: false }, { dir: -1, fire: false }],
  };
  const grid = G.grid;
  const sfx = name => emit('sfx', name);
  const boom = (x, y, big) => emit('boom', Math.round(x), Math.round(y), big ? 1 : 0);
  const debris = (x, y, c) => emit('debris', Math.round(x), Math.round(y), c);

  // ===== Карта =====
  function cellAt(c, r) { return (c < 0 || r < 0 || c >= N || r >= N) ? -1 : grid[gi(c, r)]; }
  function setCell(c, r, v) {
    if (c < 0 || r < 0 || c >= N || r >= N) return;
    const i = gi(c, r);
    if (grid[i] === v) return;
    grid[i] = v;
    G.gridVer++;
    if (track) G.changes.push(i, v);
  }

  // Карта строится на сетке разметки 52×52 (клетки по 12 px), а потом каждая клетка
  // разметки становится 2×2 клетками игры: так выстрел снимает четверть стенки, а не половину.
  // Уровни 1–35 — оригинальные карты Battle City, дальше — сгенерированные.
  function genLevel(lv) {
    const L = new Uint8Array(LN * LN);
    if (STAGES.length) classicLayout(STAGES[(lv - 1) % STAGES.length], L); else randomLayout(lv, L);
    const k = LC / CELL;
    for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) grid[gi(c, r)] = L[Math.floor(r / k) * LN + Math.floor(c / k)];
    setRing(BRICK);
    G.gridVer++;
    G.fullGrid = true;
    G.changes.length = 0;
  }

  // Оригинальная карта: 13×13 тайлов, тайл — 4×4 клетки разметки (формат описан в stages.js)
  function classicLayout(stage, L) {
    const fill = (c, r, w, h, t) => { for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) L[y * LN + x] = t; };
    const TILE = { x: EMPTY, f: BUSH, r: WATER, s: ICE, e: BASE };
    stage.map.forEach((line, row) => line.trim().toLowerCase().split(/ +/).forEach((item, col) => {
      const c = col * 4, r = row * 4, kind = item[0], hex = item.slice(1);
      if (kind === 'b') {
        // четверти тайла: верх-лево, верх-право, низ-лево, низ-право; в каждой 2×2 кирпичика
        const quarters = hex.length === 1 ? [1, 2, 4, 8].map(q => parseInt(hex, 16) & q ? 0xf : 0)
                                          : Array.from(hex, h => parseInt(h, 16));
        quarters.forEach((m, q) => {
          for (let i = 0; i < 4; i++) if (m & (1 << i)) fill(c + (q % 2) * 2 + (i % 2), r + (q >> 1) * 2 + (i >> 1), 1, 1, BRICK);
        });
      } else if (kind === 't') {
        const m = parseInt(hex, 16);
        for (let q = 0; q < 4; q++) if (m & (1 << q)) fill(c + (q % 2) * 2, r + (q >> 1) * 2, 2, 2, STEEL);
      } else {
        fill(c, r, 4, 4, TILE[kind] !== undefined ? TILE[kind] : EMPTY);
      }
    }));
  }

  function randomLayout(lv, L) {
    const li = (c, r) => r * LN + c;
    const R = mulberry32(lv * 7919 + 13);
    const ri = (a, b) => a + Math.floor(R() * (b - a + 1));
    const put = (c, r, w, h, t) => {
      for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) {
        if (x >= 0 && y >= 0 && x < LN && y < LN) { L[li(x, y)] = t; L[li(LN - 1 - x, y)] = t; }
      }
    };
    const steelP = Math.min(0.1 + lv * 0.015, 0.22), waterP = lv > 1 ? 0.08 : 0.04, bushP = 0.12;
    const pieces = 12 + Math.min(lv * 2, 18);
    for (let i = 0; i < pieces; i++) {
      const r = R();
      const t = r < steelP ? STEEL : r < steelP + waterP ? WATER : r < steelP + waterP + bushP ? BUSH : BRICK;
      const thick = (t === BUSH || t === WATER || R() < 0.5) ? 4 : 2;
      const len = ri(2, 8) * 2;
      const horiz = R() < 0.5;
      put(ri(0, 12) * 2, ri(2, 22) * 2, horiz ? len : thick, horiz ? thick : len, t);
    }
    // Отдельные кирпичные блоки для разнообразия
    for (let i = 0; i < 6; i++) put(ri(1, 11) * 2, ri(3, 20) * 2, 4, 4, BRICK);
    // Небольшие бетонные блоки
    for (let i = 0; i < 4 + Math.min(lv, 6); i++) put(ri(1, 11) * 2, ri(3, 21) * 2, ri(1, 2) * 2, 2, STEEL);

    const clear = (c, r, w, h) => { for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) L[li(x, y)] = EMPTY; };
    const soften = (c, r, w, h) => {
      for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) {
        const v = L[li(x, y)];
        if (v === STEEL || v === WATER) L[li(x, y)] = BRICK;
      }
    };
    // Точки появления врагов и проходы от них
    for (const sx of SPAWNS) { clear(sx / LC, 0, 4, 4); soften(sx / LC, 4, 4, 14); }
    // Зона штаба и игроков
    clear(20, 42, 12, 10);
    clear(16, 48, 4, 4); clear(32, 48, 4, 4);
    soften(16, 0, 4, 48); soften(32, 0, 4, 48);
    for (let y = 48; y < 52; y++) for (let x = 24; x < 28; x++) L[li(x, y)] = BASE;
    // Бетонное прикрытие штаба: нет прямого прострела сверху и с боков
    put(22, ri(13, 19) * 2, 8, 2, STEEL);
    if (R() < 0.5) put(22, ri(4, 9) * 2, 8, 2, STEEL);
    put(ri(2, 6) * 2, 46, 2, 6, STEEL);
  }
  function ringCells() {
    const out = [];
    // кольцо в полтайла вокруг штаба (штаб — клетки 48–55 × 96–103)
    for (let y = 92; y < 104; y++) for (let x = 44; x < 60; x++) {
      if (x >= 48 && x < 56 && y >= 96) continue;
      out.push([x, y]);
    }
    return out;
  }
  function setRing(t) {
    const tanks = allTanks();
    for (const [x, y] of ringCells()) {
      if (tanks.some(k => rectsOverlap(x * CELL, y * CELL, CELL, CELL, k.x, k.y, TS, TS))) continue;
      setCell(x, y, t);
    }
  }

  // ===== Столкновения =====
  function cellsIn(x, y, w, h, cb) {
    const c0 = Math.floor(x / CELL), c1 = Math.floor((x + w - 0.01) / CELL);
    const r0 = Math.floor(y / CELL), r1 = Math.floor((y + h - 0.01) / CELL);
    for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) if (cb(c, r, cellAt(c, r))) return true;
    return false;
  }
  const tankSolid = v => v === BRICK || v === STEEL || v === WATER || v === BASE || v < 0;
  function allTanks() { return G.players.filter(p => p.alive).concat(G.enemies.filter(e => e.alive)); }
  function overlapsTank(x, y, o) { return rectsOverlap(x, y, TS, TS, o.x, o.y, TS, TS); }

  function blocked(t, x, y, px = t.x, py = t.y) {
    if (x < 0 || y < 0 || x > FS - TS || y > FS - TS) return true;
    if (cellsIn(x, y, TS, TS, (c, r, v) => tankSolid(v))) return true;
    for (const o of allTanks()) {
      if (o !== t && overlapsTank(x, y, o) && !overlapsTank(px, py, o)) return true;
    }
    return false;
  }
  function moveTank(t, dist) {
    const dx = DX[t.dir], dy = DY[t.dir];
    let moved = 0;
    while (dist > 0) {
      const s = Math.min(1, dist);
      const nx = t.x + dx * s, ny = t.y + dy * s;
      if (blocked(t, nx, ny)) break;
      t.x = nx; t.y = ny; dist -= s; moved += s;
    }
    return moved;
  }
  function turn(t, d) {
    if (t.dir === d) return;
    if ((t.dir % 2) !== (d % 2)) {
      // при повороте выравниваем по сетке в полтайла, чтобы танк проходил в проходы
      const ox = t.x, oy = t.y;
      if (d % 2 === 0) t.x = Math.round(t.x / 24) * 24; else t.y = Math.round(t.y / 24) * 24;
      if (blocked(t, t.x, t.y, ox, oy)) { t.x = ox; t.y = oy; }
    }
    t.dir = d;
  }

  // ===== Игроки и враги =====
  function makePlayer(id) {
    return { id, isPlayer: true, lives: 3, score: 0, level: 0, x: 0, y: 0, dir: 0, speed: 108, alive: true,
             respawn: 0, shield: 0, anim: 0, cool: 0, bullets: 0, maxB: 1, bspeed: 340, power: 1, stun: 0, stunSide: 1, slide: 0,
             frozen: 0, kills: [0, 0, 0, 0], extraLife: false };
  }
  function addScore(p, n) {
    p.score += n;
    if (!p.extraLife && p.score >= EXTRA_LIFE_SCORE) {
      p.extraLife = true;
      p.lives++;
      sfx('power');
      emit('popup', Math.round(p.x + 24), Math.round(p.y + 8), '1UP');
    }
  }
  function applyStats(p) {
    p.bspeed = p.level >= 1 ? 540 : 340;
    p.maxB = p.level >= 2 ? 2 : 1;
    p.power = p.level >= 3 ? 2 : 1;
  }
  function spawnPlayer(p) {
    p.x = p.id ? 384 : 192; p.y = 576; p.dir = 0;
    p.alive = true; p.shield = 3; p.respawn = 0; p.cool = 0; p.stun = 0; p.slide = 0; p.frozen = 0;
    applyStats(p);
  }
  // Номер круга: после 35-го уровня карты идут заново с 1-й, а враги становятся сильнее
  const lapOf = lv => STAGES.length ? Math.floor((lv - 1) / STAGES.length) : 0;
  function makeEnemy(s) {
    const T = ETYPES[s.type];
    const speedUp = (1 + Math.min(G.level - 1, 10) * 0.025) * (1 + 0.1 * Math.min(lapOf(G.level), 4));
    return { id: ++G.nextId, x: s.x, y: s.y, dir: 2, isPlayer: false, type: s.type, hp: T.hp,
             speed: T.speed * speedUp, bspeed: T.bspeed, maxB: 1, power: 1,
             bullets: 0, cool: 0, anim: 0, bonus: s.bonus, ai: rand(0.5, 2), shootT: rand(0.4, 1.2),
             score: T.score, alive: true, stun: 0, stunSide: 1 };
  }
  function buildQueue(lv) {
    // оригинальный уровень: враги в том порядке, что и в Battle City;
    // на следующих кругах часть врагов заменяется на более сильный тип
    if (STAGES.length) {
      const lap = lapOf(lv), R = mulberry32(lv * 131 + 7), out = [];
      for (const g of STAGES[(lv - 1) % STAGES.length].bots) {
        const [n, type] = g.split('*');
        for (let i = 0; i < +n; i++) {
          let t = BOT_TYPES[type.trim()];
          if (t < 3 && R() < Math.min(lap * 0.25, 0.75)) t++;
          out.push(t);
        }
      }
      return out;
    }
    const R = mulberry32(lv * 31 + 5), q = [];
    const a = Math.min(0.02 + lv * 0.03, 0.3), p = Math.min(0.04 + lv * 0.03, 0.3), f = Math.min(0.12 + lv * 0.02, 0.3);
    for (let i = 0; i < 20; i++) {
      const r = R();
      q.push(r < a ? 3 : r < a + p ? 2 : r < a + p + f ? 1 : 0);
    }
    return q;
  }
  function trySpawn() {
    if (!G.queue.length) return;
    const maxOn = G.twoP ? 6 : 4;
    if (G.enemies.length + G.stars.length >= maxOn) return;
    for (let k = 0; k < 3; k++) {
      const x = SPAWNS[(G.spawnIdx + k) % 3];
      if (!G.stars.some(s => s.x === x)) {
        G.spawnIdx = (G.spawnIdx + k + 1) % 3;
        const n = 20 - G.queue.length, bonus = n === 3 || n === 10 || n === 17;
        if (bonus) G.powerups = [];                // как в оригинале: новый бонусный танк убирает старый бонус
        G.stars.push({ x, y: 0, t: 1, type: G.queue.shift(), bonus });
        return;
      }
    }
  }

  // ===== Ход игры =====
  function startGame(two, fromLevel = 1) {
    G.twoP = !!two;
    G.players = [makePlayer(0)];
    if (two) G.players.push(makePlayer(1));
    G.level = Math.max(1, Math.floor(fromLevel) || 1);
    for (const i of G.inputs) { i.dir = -1; i.fire = false; }
    startLevel();
  }
  function startLevel() {
    G.enemies = []; G.bullets = []; G.powerups = []; G.stars = [];
    genLevel(G.level);
    G.queue = buildQueue(G.level);
    G.spawnIdx = 0; G.spawnTimer = 0.2; G.freeze = 0; G.shovel = 0; G.baseAlive = true; G.paused = false;
    G.stageTime = 0; G.tallyBonus = -1;
    for (const p of G.players) {
      p.bullets = 0;
      p.kills = [0, 0, 0, 0];
      if (p.alive || p.respawn > 0) spawnPlayer(p);
    }
    G.state = 'intro'; G.stateT = 2;
    sfx('start');
  }

  function fire(t) {
    if (t.cool > 0 || t.bullets >= t.maxB) return;
    G.bullets.push({ id: ++G.nextId, x: t.x + 24 + DX[t.dir] * 22, y: t.y + 24 + DY[t.dir] * 22, dir: t.dir, speed: t.bspeed,
                     owner: t, power: t.power, player: t.isPlayer });
    t.bullets++;
    t.cool = t.isPlayer ? 0.12 : 0.3;
    if (t.isPlayer) sfx('shoot');
  }

  function pickDir(e, avoid) {
    const r = Math.random(), cx = e.x + 24, cy = e.y + 24;
    const toward = (tx, ty) => {
      const ax = Math.abs(tx - cx), ay = Math.abs(ty - cy);
      if (ax > 12 && (ax > ay || Math.random() < 0.4)) return tx > cx ? 1 : 3;
      return ty > cy ? 2 : 0;
    };
    const alive = G.players.filter(p => p.alive);
    // как в оригинале: чем дольше идёт уровень, тем настойчивее враги идут к штабу
    const baseP = Math.min(0.2 + G.stageTime / 150, 0.7), playerP = Math.min(0.25, 0.9 - baseP);
    let d;
    if (r < baseP) d = toward(BASE_X + 24, BASE_Y + 24);
    else if (r < baseP + playerP && alive.length) {
      const p = alive[Math.floor(Math.random() * alive.length)];
      d = toward(p.x + 24, p.y + 24);
    } else d = Math.floor(Math.random() * 4);
    // упёрся — не пытаться ехать туда же
    if (avoid && d === e.dir) d = (e.dir + 1 + Math.floor(Math.random() * 3)) % 4;
    turn(e, d);
  }

  // Враг едет до следующей границы полутайла (24 px) и только там может сменить направление
  function enemyMove(e, dt) {
    e.ai -= dt;
    const want = e.speed * dt;
    const vert = e.dir % 2 === 0, pos = vert ? e.y : e.x, fwd = e.dir === 1 || e.dir === 2;
    const next = fwd ? Math.floor(pos / 24 + 1e-6) * 24 + 24 : Math.ceil(pos / 24 - 1e-6) * 24 - 24;
    const dist = Math.abs(next - pos);
    const step = Math.min(want, dist);
    const m = moveTank(e, step);
    e.anim += m;
    if (m < step - 0.01) {
      e.shootT -= dt * 2;                      // упёрся — чаще стреляет, чтобы пробить кирпич
      e.blockedT = (e.blockedT || 0) + dt;
      if (e.blockedT > 0.25) { e.blockedT = 0; pickDir(e, true); e.ai = rand(0.6, 2.2); }
      return;
    }
    e.blockedT = 0;
    if (step >= dist - 1e-6) {
      if (vert) e.y = next; else e.x = next;   // ровно на границе
      if (e.ai <= 0) { pickDir(e); e.ai = rand(0.6, 2.2); }
    }
  }

  function enemyAI(e, dt) {
    if (e.stun <= 0) enemyMove(e, dt);         // с перебитой гусеницей стоит, но стреляет

    // прицел: игрок или штаб на линии огня
    const cx = e.x + 24, cy = e.y + 24;
    const inLine = (tx, ty) => {
      if (e.dir % 2 === 0) return Math.abs(tx - cx) < 18 && (e.dir === 0 ? ty < cy : ty > cy);
      return Math.abs(ty - cy) < 18 && (e.dir === 3 ? tx < cx : tx > cx);
    };
    if (G.players.some(p => p.alive && inLine(p.x + 24, p.y + 24)) || inLine(BASE_X + 24, BASE_Y + 24)) {
      e.shootT = Math.min(e.shootT, 0.12);
    }
    e.shootT -= dt;
    if (e.shootT <= 0) {
      fire(e);
      e.shootT = rand(0.5, 1.7) * Math.max(0.5, 1 - G.level * 0.04);
    }
  }

  function killEnemy(e, by) {
    e.alive = false;
    boom(e.x + 24, e.y + 24, true);
    sfx('boom');
    if (by) {
      by.kills[e.type]++;
      addScore(by, e.score);
      emit('popup', Math.round(e.x + 24), Math.round(e.y + 24), String(e.score));
    }
  }
  function hitEnemy(e, by) {
    if (e.bonus) { e.bonus = false; spawnPowerup(); }
    e.hp--;
    if (e.hp > 0) { sfx('armor'); return; }
    killEnemy(e, by);
  }
  // Попадание в торец гусеницы при выстреле в лоб или в спину; выстрел в борт — обычное попадание
  function isTrackHit(t, b) {
    if ((b.dir % 2) !== (t.dir % 2)) return false;
    const lat = t.dir % 2 === 0 ? b.x - (t.x + 24) : b.y - (t.y + 24);
    return Math.abs(lat) >= 11;
  }
  function stunTank(t, b) {
    const rd = (t.dir + 1) % 4;
    t.stunSide = (b.x - t.x - 24) * DX[rd] + (b.y - t.y - 24) * DY[rd] >= 0 ? 1 : -1;
    t.stun = STUN_TIME;
    debris(b.x, b.y, '#ffb030');
    debris(b.x, b.y, '#3a3a3a');
    sfx('track');
  }
  function hitPlayer(p) {
    if (p.shield > 0) return;
    p.alive = false;
    boom(p.x + 24, p.y + 24, true);
    sfx('boom');
    emit('shake', 0.35);
    p.level = 0;
    if (p.lives > 0) { p.lives--; p.respawn = 1.6; }
  }
  function destroyBase() {
    if (!G.baseAlive) return;
    G.baseAlive = false;
    boom(BASE_X + 24, BASE_Y + 24, true);
    boom(BASE_X + 10, BASE_Y + 30, true);
    boom(BASE_X + 38, BASE_Y + 18, true);
    sfx('boom');
    emit('shake', 0.7);
  }

  // ===== Бонусы =====
  function spawnPowerup() {
    let x, y, tries = 0;
    do {
      x = Math.floor(Math.random() * 25) * 24;
      y = Math.floor(Math.random() * 22) * 24;
      tries++;
    } while (tries < 30 && rectsOverlap(x, y, TS, TS, 216, 528, 192, 96));
    const types = Object.keys(PU_WEIGHTS), total = types.reduce((s, k) => s + PU_WEIGHTS[k], 0);
    let r = Math.random() * total, type = types[0];
    for (const k of types) { r -= PU_WEIGHTS[k]; if (r < 0) { type = k; break; } }
    G.powerups = [{ type, x, y, t: 18 }];
    sfx('bonusAppear');
  }
  function applyPU(p, type) {
    addScore(p, 500);
    emit('popup', Math.round(p.x + 24), Math.round(p.y + 24), '500');
    sfx('power');
    switch (type) {
      case 'helmet': p.shield = 10; break;
      case 'star': p.level = Math.min(3, p.level + 1); applyStats(p); break;
      case 'grenade': for (const e of G.enemies) if (e.alive) killEnemy(e, null); emit('shake', 0.4); break;
      case 'clock': G.freeze = 10; break;
      case 'shovel': G.shovel = 18; setRing(STEEL); break;
      case 'tank': p.lives++; break;
    }
  }

  // ===== Пули =====
  function killBullet(b, explode) {
    b.dead = true;
    if (explode) boom(b.x, b.y, false);
  }
  function hitCell(c, r, power) {
    const v = cellAt(c, r);
    if (v === BRICK) { setCell(c, r, EMPTY); if (c % 2) debris(c * CELL, r * CELL + 3, '#b5562a'); return 1; }
    if (v === STEEL) {
      if (power >= 2) { setCell(c, r, EMPTY); if (c % 2) debris(c * CELL, r * CELL + 3, '#cfcfcf'); return 1; }
      return 2;
    }
    return 0;
  }
  function impact(b) {
    // Пуля сносит полосу шириной с танк (8 клеток) и глубиной в одну клетку (6 px)
    // в первом ряду, где есть что ломать: стенка в полтайла уходит за 4 выстрела
    const vert = b.dir % 2 === 0;
    const lead = vert ? Math.floor((b.dir === 0 ? b.y - 3 : b.y + 2.99) / CELL)
                      : Math.floor((b.dir === 3 ? b.x - 3 : b.x + 2.99) / CELL);
    const c0 = Math.round((vert ? b.x : b.y) / CELL) - 4;
    let broke = false, steel = false;
    for (const line of [lead, lead - (vert ? DY[b.dir] : DX[b.dir])]) {
      for (let k = c0; k < c0 + 8; k++) {
        const res = vert ? hitCell(k, line, b.power) : hitCell(line, k, b.power);
        if (res === 1) broke = true; else if (res === 2) steel = true;
      }
      if (broke || steel) break;
    }
    if (broke) sfx('brick'); else if (steel && b.player) sfx('steel');
  }
  function bulletStep(b) {
    if (b.x < 0 || b.y < 0 || b.x > FS || b.y > FS) {
      killBullet(b, true);
      if (b.player) sfx('steel');
      return;
    }
    let hit = false, base = false;
    cellsIn(b.x - 3, b.y - 3, 6, 6, (c, r, v) => {
      if (v === BRICK || v === STEEL) hit = true;
      if (v === BASE) base = true;
      return false;
    });
    if (base) { killBullet(b, true); destroyBase(); return; }
    if (hit) { impact(b); killBullet(b, true); return; }
    for (const t of allTanks()) {
      // пуля 6×6: задевшая край танка (торец гусеницы) — тоже попадание
      if (t === b.owner || !rectsOverlap(b.x - 3, b.y - 3, 6, 6, t.x, t.y, TS, TS)) continue;
      if (b.player !== t.isPlayer) {
        if (t.isPlayer && t.shield > 0) { killBullet(b, true); return; }
        if (TRACK_HITS && isTrackHit(t, b)) {
          if (!t.isPlayer && t.bonus) { t.bonus = false; spawnPowerup(); }
          stunTank(t, b);
          killBullet(b, true);
          return;
        }
        if (b.player) hitEnemy(t, b.owner); else hitPlayer(t);
        killBullet(b, t.alive);
        return;
      }
      if (b.player && t.isPlayer) {
        // как в оригинале: подбитый напарником танк на время замирает (стрелять может)
        if (t.shield <= 0) { t.frozen = PARTNER_FREEZE; sfx('armor'); }
        killBullet(b, true);
        return;
      }
      // вражеские пули пролетают сквозь своих
    }
  }
  function updateBullets(dt) {
    for (const b of G.bullets) {
      let dist = b.speed * dt;
      while (dist > 0 && !b.dead) {
        const s = Math.min(4, dist);
        dist -= s;
        b.x += DX[b.dir] * s; b.y += DY[b.dir] * s;
        bulletStep(b);
      }
    }
    const bs = G.bullets;
    for (let i = 0; i < bs.length; i++) for (let j = i + 1; j < bs.length; j++) {
      const a = bs[i], c = bs[j];
      if (a.dead || c.dead || a.player === c.player) continue;
      if (Math.abs(a.x - c.x) < 8 && Math.abs(a.y - c.y) < 8) { killBullet(a, true); killBullet(c, false); }
    }
    G.bullets = bs.filter(b => { if (b.dead) { b.owner.bullets--; return false; } return true; });
  }

  // ===== Обновление =====
  function update(dt) {
    if (G.freeze > 0) G.freeze -= dt;
    G.stageTime += dt;
    for (const p of G.players) {
      if (!p.alive) {
        if (p.respawn > 0) { p.respawn -= dt; if (p.respawn <= 0) spawnPlayer(p); }
        continue;
      }
      p.cool -= dt;
      if (p.shield > 0) p.shield -= dt;
      if (p.stun > 0) p.stun -= dt;
      if (p.frozen > 0) p.frozen -= dt;
      const canMove = p.stun <= 0 && p.frozen <= 0;
      if (!G.baseAlive) continue;
      const inp = G.inputs[p.id];
      const onIce = cellAt(Math.floor((p.x + 24) / CELL), Math.floor((p.y + 24) / CELL)) === ICE;
      if (inp.dir >= 0 && canMove) {
        turn(p, inp.dir);
        p.anim += moveTank(p, p.speed * dt);
        p.slide = onIce ? ICE_SLIDE : 0;
      } else if (p.slide > 0 && canMove && onIce) {
        // на льду танк по инерции проезжает ещё немного
        p.slide -= dt;
        if (moveTank(p, p.speed * dt) === 0) p.slide = 0;
      } else p.slide = 0;
      if (inp.fire) fire(p);
      for (const u of G.powerups) {
        if (!u.taken && rectsOverlap(p.x + 6, p.y + 6, 36, 36, u.x, u.y, TS, TS)) { u.taken = true; applyPU(p, u.type); }
      }
    }
    G.powerups = G.powerups.filter(u => !u.taken && (u.t -= dt) > 0);

    for (const e of G.enemies) {
      e.cool -= dt;
      if (e.stun > 0) e.stun -= dt;
      if (G.freeze > 0 || !e.alive) continue;
      enemyAI(e, dt);
    }
    for (const s of G.stars) {
      s.t -= dt;
      if (s.t <= 0) {
        if (allTanks().some(k => overlapsTank(s.x, s.y, k))) s.t = 0.1;
        else { G.enemies.push(makeEnemy(s)); s.done = true; }
      }
    }
    G.stars = G.stars.filter(s => !s.done);
    if (G.state === 'play') {
      G.spawnTimer -= dt;
      if (G.spawnTimer <= 0) { trySpawn(); G.spawnTimer = Math.max(1.1, 2.8 - G.level * 0.12); }
    }

    updateBullets(dt);
    G.enemies = G.enemies.filter(e => e.alive);

    if (G.shovel > 0) {
      G.shovel -= dt;
      if (G.shovel <= 0) setRing(BRICK);
      else if (G.shovel < 3) setRing(Math.floor(G.shovel * 5) % 2 ? STEEL : BRICK);
    }

    if (G.state === 'play') {
      if (!G.baseAlive || G.players.every(p => !p.alive && p.respawn <= 0)) {
        G.state = 'dying'; G.stateT = 3;
        sfx('over');
      } else if (!G.queue.length && !G.enemies.length && !G.stars.length) {
        G.state = 'done'; G.stateT = DONE_TIME;
        // при игре вдвоём тот, кто уничтожил больше врагов, получает бонус
        if (G.players.length === 2) {
          const [a, b] = G.players.map(p => p.kills.reduce((s, k) => s + k, 0));
          if (a !== b) { G.tallyBonus = a > b ? 0 : 1; addScore(G.players[G.tallyBonus], TALLY_BONUS); }
        }
        sfx('win');
      }
    }
  }

  function tick(dt) {
    switch (G.state) {
      case 'intro':
        if (!G.paused) { G.stateT -= dt; if (G.stateT <= 0) G.state = 'play'; }
        break;
      case 'play':
        if (!G.paused) update(dt);
        break;
      case 'dying':
        update(dt);
        G.stateT -= dt;
        if (G.stateT <= 0) { G.state = 'over'; G.stateT = 1; }
        break;
      case 'done':
        update(dt);
        G.stateT -= dt;
        if (G.stateT <= 0) { G.level++; startLevel(); }
        break;
      case 'over':
        if (G.stateT > 0) G.stateT -= dt;
        break;
    }
  }

  function setInput(pid, dir, fireOn) {
    const i = G.inputs[pid];
    if (!i) return;
    i.dir = Number.isInteger(dir) && dir >= 0 && dir <= 3 ? dir : -1;
    i.fire = !!fireOn;
  }
  function togglePause() {
    if (G.state === 'play' || G.state === 'intro') G.paused = !G.paused;
  }

  return { G, startGame, tick, setInput, togglePause };
}

const api = { createGame, CELL, N, FS, TS, EMPTY, BRICK, STEEL, WATER, BUSH, ICE, BASE, DX, DY, BASE_X, BASE_Y, STUN_TIME,
              CLASSIC_STAGES: STAGES.length, ETYPES, DONE_TIME, TALLY_DELAY, TALLY_BONUS, PARTNER_FREEZE };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.Tanks = api;
})(typeof self !== 'undefined' ? self : this);
