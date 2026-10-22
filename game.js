// Логика игры «Танки». Общая для браузера (одиночная игра) и сервера (сетевая игра).
// Не трогает DOM: звуки и визуальные эффекты отдаются наружу через emit(...).
(function (root) {
'use strict';

const CELL = 12, N = 52, FS = CELL * N, TS = 48;        // клетка, клеток по стороне, размер поля, размер танка
const EMPTY = 0, BRICK = 1, STEEL = 2, WATER = 3, BUSH = 4, BASE = 6;
const DX = [0, 1, 0, -1], DY = [-1, 0, 1, 0];          // 0 вверх, 1 вправо, 2 вниз, 3 влево
const BASE_X = 288, BASE_Y = 576;
const SPAWNS = [0, 288, 576];
const STUN_TIME = 3;
const ETYPES = [
  { speed: 48,  bspeed: 260, hp: 1, score: 100 }, // обычный
  { speed: 100, bspeed: 300, hp: 1, score: 200 }, // быстрый
  { speed: 58,  bspeed: 450, hp: 1, score: 300 }, // скорострельный
  { speed: 46,  bspeed: 300, hp: 4, score: 400 }, // броневик
];
const PU_TYPES = ['helmet', 'star', 'grenade', 'clock', 'shovel', 'tank'];

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
    spawnTimer: 0, spawnIdx: 0, nextId: 0, freeze: 0, shovel: 0, baseAlive: true,
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

  function genLevel(lv) {
    grid.fill(EMPTY);
    const R = mulberry32(lv * 7919 + 13);
    const ri = (a, b) => a + Math.floor(R() * (b - a + 1));
    const put = (c, r, w, h, t) => {
      for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) {
        if (x >= 0 && y >= 0 && x < N && y < N) { grid[gi(x, y)] = t; grid[gi(N - 1 - x, y)] = t; }
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

    const clear = (c, r, w, h) => { for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) grid[gi(x, y)] = EMPTY; };
    const soften = (c, r, w, h) => {
      for (let y = r; y < r + h; y++) for (let x = c; x < c + w; x++) {
        const v = grid[gi(x, y)];
        if (v === STEEL || v === WATER) grid[gi(x, y)] = BRICK;
      }
    };
    // Точки появления врагов и проходы от них
    for (const sx of SPAWNS) { clear(sx / CELL, 0, 4, 4); soften(sx / CELL, 4, 4, 14); }
    // Зона штаба и игроков
    clear(20, 42, 12, 10);
    clear(16, 48, 4, 4); clear(32, 48, 4, 4);
    soften(16, 0, 4, 48); soften(32, 0, 4, 48);
    for (let y = 48; y < 52; y++) for (let x = 24; x < 28; x++) grid[gi(x, y)] = BASE;
    setRing(BRICK);
    // Бетонное прикрытие штаба: нет прямого прострела сверху и с боков
    put(22, ri(13, 19) * 2, 8, 2, STEEL);
    if (R() < 0.5) put(22, ri(4, 9) * 2, 8, 2, STEEL);
    put(ri(2, 6) * 2, 46, 2, 6, STEEL);
    G.gridVer++;
    G.fullGrid = true;
    G.changes.length = 0;
  }
  function ringCells() {
    const out = [];
    for (let y = 46; y < 52; y++) for (let x = 22; x < 30; x++) {
      if (x >= 24 && x < 28 && y >= 48) continue;
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
             respawn: 0, shield: 0, anim: 0, cool: 0, bullets: 0, maxB: 1, bspeed: 340, power: 1, stun: 0, stunSide: 1 };
  }
  function applyStats(p) {
    p.bspeed = p.level >= 1 ? 540 : 340;
    p.maxB = p.level >= 2 ? 2 : 1;
    p.power = p.level >= 3 ? 2 : 1;
  }
  function spawnPlayer(p) {
    p.x = p.id ? 384 : 192; p.y = 576; p.dir = 0;
    p.alive = true; p.shield = 3; p.respawn = 0; p.cool = 0; p.stun = 0;
    applyStats(p);
  }
  function makeEnemy(s) {
    const T = ETYPES[s.type];
    return { id: ++G.nextId, x: s.x, y: s.y, dir: 2, isPlayer: false, type: s.type, hp: T.hp,
             speed: T.speed * (1 + Math.min(G.level - 1, 10) * 0.025), bspeed: T.bspeed, maxB: 1, power: 1,
             bullets: 0, cool: 0, anim: 0, bonus: s.bonus, ai: rand(0.5, 2), shootT: rand(0.4, 1.2),
             score: T.score, alive: true, stun: 0, stunSide: 1 };
  }
  function buildQueue(lv) {
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
        const n = 20 - G.queue.length;
        G.stars.push({ x, y: 0, t: 1, type: G.queue.shift(), bonus: n === 3 || n === 10 || n === 17 });
        return;
      }
    }
  }

  // ===== Ход игры =====
  function startGame(two) {
    G.twoP = !!two;
    G.players = [makePlayer(0)];
    if (two) G.players.push(makePlayer(1));
    G.level = 1;
    for (const i of G.inputs) { i.dir = -1; i.fire = false; }
    startLevel();
  }
  function startLevel() {
    G.enemies = []; G.bullets = []; G.powerups = []; G.stars = [];
    genLevel(G.level);
    G.queue = buildQueue(G.level);
    G.spawnIdx = 0; G.spawnTimer = 0.2; G.freeze = 0; G.shovel = 0; G.baseAlive = true; G.paused = false;
    for (const p of G.players) {
      p.bullets = 0;
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

  function pickDir(e) {
    const r = Math.random(), cx = e.x + 24, cy = e.y + 24;
    const toward = (tx, ty) => {
      const ax = Math.abs(tx - cx), ay = Math.abs(ty - cy);
      if (ax > 12 && (ax > ay || Math.random() < 0.4)) return tx > cx ? 1 : 3;
      return ty > cy ? 2 : 0;
    };
    const alive = G.players.filter(p => p.alive);
    let d;
    if (r < 0.4) d = toward(BASE_X + 24, BASE_Y + 24);
    else if (r < 0.65 && alive.length) {
      const p = alive[Math.floor(Math.random() * alive.length)];
      d = toward(p.x + 24, p.y + 24);
    } else d = Math.floor(Math.random() * 4);
    turn(e, d);
  }

  function enemyAI(e, dt) {
    if (e.stun <= 0) {                         // с перебитой гусеницей стоит, но стреляет
      e.ai -= dt;
      const want = e.speed * dt;
      const m = moveTank(e, want);
      e.anim += m;
      if (m < want - 0.01) {
        e.shootT -= dt * 2;                    // упёрся — чаще стреляет
        if (Math.random() < 0.06) e.ai = Math.min(e.ai, 0);
      }
      if (e.ai <= 0) { pickDir(e); e.ai = rand(0.7, 2.6); }
    }

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
      by.score += e.score;
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
    G.powerups = [{ type: PU_TYPES[Math.floor(Math.random() * PU_TYPES.length)], x, y, t: 18 }];
    sfx('bonusAppear');
  }
  function applyPU(p, type) {
    p.score += 500;
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
    if (v === BRICK) { setCell(c, r, EMPTY); debris(c * CELL + 6, r * CELL + 6, '#b5562a'); return 1; }
    if (v === STEEL) {
      if (power >= 2) { setCell(c, r, EMPTY); debris(c * CELL + 6, r * CELL + 6, '#cfcfcf'); return 1; }
      return 2;
    }
    return 0;
  }
  function impact(b) {
    // Пуля сносит полосу шириной с танк (4 клетки) в первом ряду, где есть что ломать
    const vert = b.dir % 2 === 0;
    const lead = vert ? Math.floor((b.dir === 0 ? b.y - 3 : b.y + 2.99) / CELL)
                      : Math.floor((b.dir === 3 ? b.x - 3 : b.x + 2.99) / CELL);
    const c0 = Math.round((vert ? b.x : b.y) / CELL) - 2;
    let broke = false, steel = false;
    for (const line of [lead, lead - (vert ? DY[b.dir] : DX[b.dir])]) {
      for (let k = c0; k < c0 + 4; k++) {
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
      if (t === b.owner || b.x <= t.x || b.x >= t.x + TS || b.y <= t.y || b.y >= t.y + TS) continue;
      if (b.player !== t.isPlayer) {
        if (t.isPlayer && t.shield > 0) { killBullet(b, true); return; }
        if (isTrackHit(t, b)) {
          if (!t.isPlayer && t.bonus) { t.bonus = false; spawnPowerup(); }
          stunTank(t, b);
          killBullet(b, true);
          return;
        }
        if (b.player) hitEnemy(t, b.owner); else hitPlayer(t);
        killBullet(b, t.alive);
        return;
      }
      if (b.player && t.isPlayer) { killBullet(b, true); return; }
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
    for (const p of G.players) {
      if (!p.alive) {
        if (p.respawn > 0) { p.respawn -= dt; if (p.respawn <= 0) spawnPlayer(p); }
        continue;
      }
      p.cool -= dt;
      if (p.shield > 0) p.shield -= dt;
      if (p.stun > 0) p.stun -= dt;
      if (!G.baseAlive) continue;
      const inp = G.inputs[p.id];
      if (inp.dir >= 0 && p.stun <= 0) { turn(p, inp.dir); p.anim += moveTank(p, p.speed * dt); }
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
        G.state = 'done'; G.stateT = 4;
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

const api = { createGame, CELL, N, FS, TS, EMPTY, BRICK, STEEL, WATER, BUSH, BASE, DX, DY, BASE_X, BASE_Y, STUN_TIME };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.Tanks = api;
})(typeof self !== 'undefined' ? self : this);
