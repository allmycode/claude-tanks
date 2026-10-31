// Сервер сетевой игры «Танки».
// Раздаёт index.html/game.js по HTTP и ведёт игровые комнаты на два игрока по WebSocket.
// Игра считается на сервере, клиенты присылают только нажатия и получают снимки состояния.
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const { WebSocketServer } = require('ws');
const Tanks = require('./game.js');

const PORT = Number(process.env.PORT) || 8081;
const TICK = 1000 / 60;
const STATIC = { '/': 'index.html', '/index.html': 'index.html', '/game.js': 'game.js', '/stages.js': 'stages.js' };
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8' };

// Настройки сервера: config.json рядом с server.js (или путь в TANKS_CONFIG).
// Файл перечитывается при старте каждой новой игры, так что правки действуют без перезапуска.
const CONFIG_PATH = process.env.TANKS_CONFIG || path.join(__dirname, 'config.json');
let lastConfigText = null, config = {};
function loadConfig() {
  let text;
  try { text = fs.readFileSync(CONFIG_PATH, 'utf8'); } catch (e) {
    if (lastConfigText !== '') console.log(`Настройки: ${CONFIG_PATH} не найден — используются значения по умолчанию`);
    lastConfigText = ''; config = {};
    return config;
  }
  if (text === lastConfigText) return config;
  lastConfigText = text;
  let raw;
  try { raw = JSON.parse(text.replace(/^﻿/, '')); } catch (e) {
    console.log(`Настройки: ошибка в ${CONFIG_PATH}: ${e.message} — используются значения по умолчанию`);
    config = {};
    return config;
  }
  const { weights, problems } = Tanks.sanitizeWeights(raw.powerups);
  for (const p of problems) console.log('Настройки: ' + p);
  config = { powerupWeights: weights };
  const w = weights || Tanks.PU_WEIGHTS, total = Object.values(w).reduce((s, v) => s + v, 0);
  console.log('Настройки: выпадение бонусов — ' +
    Object.keys(w).map(k => `${k} ${(100 * w[k] / total).toFixed(1)}%`).join(', '));
  return config;
}

const server = http.createServer((req, res) => {
  const file = STATIC[req.url.split('?')[0]];
  if (!file) { res.writeHead(404); res.end('Not found'); return; }
  fs.readFile(path.join(__dirname, file), (err, data) => {
    if (err) { res.writeHead(500); res.end(); return; }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(file)], 'Cache-Control': 'no-cache' });
    res.end(data);
  });
});

const wss = new WebSocketServer({ server, maxPayload: 4096 });
let waiting = null;
let roomCount = 0;

function send(ws, msg) { if (ws.readyState === 1) ws.send(JSON.stringify(msg)); }
function log(...a) { console.log(new Date().toLocaleTimeString(), ...a); }

// Лобби: первый ждёт, второй сразу попадает с ним в комнату
function joinLobby(ws) {
  ws.room = null;
  if (waiting && waiting !== ws && waiting.readyState === 1) {
    const other = waiting;
    waiting = null;
    startRoom([other, ws]);
  } else {
    waiting = ws;
    send(ws, { t: 'wait' });
  }
}

const r1 = v => Math.round(v * 10) / 10;
function snapshot(G, events) {
  const m = {
    t: 's', st: G.state, stT: r1(G.stateT), lv: G.level, pa: G.paused, fr: r1(G.freeze), ba: G.baseAlive, q: G.queue,
    pl: G.players.map(p => [p.alive ? 1 : 0, r1(p.x), r1(p.y), p.dir, p.lives, p.score, p.level,
                            r1(p.shield), r1(p.stun), p.stunSide, r1(p.anim % 6), r1(p.frozen), p.kills]),
    tb: G.tallyBonus,
    en: G.enemies.map(e => [r1(e.x), r1(e.y), e.dir, e.type, e.hp, e.bonus ? 1 : 0, r1(e.stun), e.stunSide, r1(e.anim % 6), e.id]),
    bu: G.bullets.map(b => [r1(b.x), r1(b.y), b.dir, b.player ? 1 : 0, b.id]),
    pu: G.powerups.map(u => [u.type, u.x, u.y, r1(u.t)]),
    sr: G.stars.map(s => s.x),
    ev: events,
  };
  if (G.fullGrid) { m.g = Array.from(G.grid).join(''); G.fullGrid = false; G.changes.length = 0; }
  else if (G.changes.length) { m.gc = G.changes.slice(); G.changes.length = 0; }
  return m;
}

function startRoom(clients) {
  const id = ++roomCount;
  const events = [];
  const game = Tanks.createGame({ emit: (...ev) => events.push(ev), trackChanges: true,
                                  powerupWeights: loadConfig().powerupWeights });
  const room = { id, clients, game };
  clients.forEach((c, i) => { c.room = room; c.slot = i; send(c, { t: 'start', slot: i }); });
  game.startGame(true);
  log(`комната #${id}: игра началась`);

  let last = process.hrtime.bigint();
  room.timer = setInterval(() => {
    const now = process.hrtime.bigint();
    const dt = Math.min(0.05, Number(now - last) / 1e9);
    last = now;
    game.tick(dt);
    const msg = JSON.stringify(snapshot(game.G, events));
    events.length = 0;
    for (const c of clients) if (c.readyState === 1) c.send(msg);
  }, TICK);

  room.leave = ws => {
    clearInterval(room.timer);
    log(`комната #${id}: игрок отключился, комната закрыта`);
    for (const c of clients) {
      c.room = null;
      if (c !== ws && c.readyState === 1) { send(c, { t: 'left' }); joinLobby(c); }
    }
  };
}

function onMessage(ws, m) {
  const room = ws.room;
  if (!room || !m) return;
  switch (m.t) {
    case 'in': room.game.setInput(ws.slot, m.d, m.f); break;
    case 'pause': room.game.togglePause(); break;
    case 'restart':
      if (room.game.G.state === 'over' && room.game.G.stateT <= 0) room.game.startGame(true);
      break;
  }
}

wss.on('connection', (ws, req) => {
  log('подключение', req.socket.remoteAddress);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });
  ws.on('message', data => {
    let m;
    try { m = JSON.parse(data); } catch (e) { return; }
    onMessage(ws, m);
  });
  ws.on('close', () => {
    if (waiting === ws) waiting = null;
    if (ws.room) ws.room.leave(ws);
  });
  joinLobby(ws);
});

// Отключаем «зависшие» соединения
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
}, 10000);

server.listen(PORT, () => {
  console.log(`Сервер «Танки» запущен на порту ${PORT}`);
  console.log(`  на этом компьютере:  http://localhost:${PORT}`);
  for (const list of Object.values(os.networkInterfaces())) {
    for (const a of list || []) {
      if (a.family === 'IPv4' && !a.internal) console.log(`  в локальной сети:    http://${a.address}:${PORT}`);
    }
  }
  console.log('В меню игры выберите «ПО СЕТИ» и укажите адрес сервера.');
  loadConfig();
});
