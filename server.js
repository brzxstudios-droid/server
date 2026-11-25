'use strict';
// ===== Roube el Posei - servidor multiplayer (ARQUIVO ÚNICO) =====
// Sem dependências: só precisa do Node 18+. Fala WebSocket por conta própria.
//
// COMO HOSPEDAR DE GRAÇA NO RENDER:
//  1. Crie um repositório no GitHub e suba só este arquivo (server.js) na raiz.
//  2. Em render.com: New + > Web Service > escolha o repositório.
//  3. Runtime: Node · Build Command: echo ok · Start Command: node server.js · Plano: Free.
//  4. Copie o endereço (https://xxx.onrender.com) e, no jogo (botão 🌐), digite wss://xxx.onrender.com
//  (Grátis: dorme após ~15 min sem uso; a 1ª conexão pode levar ~1 min. O placar zera ao reiniciar.)
//
// REGRAS: salas de até 12; assalto só dentro do cercado (espera 40s, vítima protegida 90s, dono por perto te pega);
// tackle a ≤110px de quem carrega Posei (espera 2,5s). Moedas/roubos vêm do celular (sem anti-trapaça forte).
const http = require('http'), crypto = require('crypto'), fs = require('fs'), path = require('path');
const PORT = process.env.PORT || 8080;
const MAX_ROOM = 12, MAX_ROOMS = 300, MAX_CONN = 600;
const PEN_TOP = 2480, PEN_BOTTOM = 2900;           // zona do cercado (igual ao jogo)
const RAID_COOLDOWN = 40000, RAID_IMMUNE = 90000, RAID_GUARD_DIST = 260;
const TACKLE_DIST = 110, TACKLE_COOLDOWN = 2500, TACKLE_IMMUNE = 5000;
const SCORES_FILE = path.join(__dirname, 'scores.json');

const rooms = new Map();            // código -> { code, players: Map(id -> client), rosterDirty }
const globalTop = new Map();        // uid -> { n, s, c, l }
let nextId = 1, conns = 0;
try { const j = JSON.parse(fs.readFileSync(SCORES_FILE, 'utf8')); for (const k in j) globalTop.set(k, j[k]); } catch (e) {}
let scoresDirty = false;

// ---------- WebSocket (RFC 6455, o mínimo necessário) ----------
function wsSend(c, obj) {
  if (!c.sock || c.sock.destroyed) return;
  const data = Buffer.from(JSON.stringify(obj)), n = data.length;
  let head;
  if (n < 126) head = Buffer.from([0x81, n]);
  else if (n < 65536) { head = Buffer.alloc(4); head[0] = 0x81; head[1] = 126; head.writeUInt16BE(n, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x81; head[1] = 127; head.writeBigUInt64BE(BigInt(n), 2); }
  try { c.sock.write(Buffer.concat([head, data])); } catch (e) {}
}
function wsCtl(c, op, payload) {
  if (!c.sock || c.sock.destroyed) return;
  const p = payload || Buffer.alloc(0);
  try { c.sock.write(Buffer.concat([Buffer.from([0x80 | op, p.length]), p])); } catch (e) {}
}
function onData(c, chunk) {
  c.buf = c.buf.length ? Buffer.concat([c.buf, chunk]) : chunk;
  if (c.buf.length > 70000) return c.sock.destroy();
  for (;;) {
    const b = c.buf;
    if (b.length < 2) return;
    const fin = !!(b[0] & 0x80), op = b[0] & 0x0f, masked = !!(b[1] & 0x80);
    let len = b[1] & 0x7f, off = 2;
    if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
    else if (len === 127) { if (b.length < 10) return; const big = b.readBigUInt64BE(2); if (big > 65536n) return c.sock.destroy(); len = Number(big); off = 10; }
    if (!masked) return c.sock.destroy();            // clientes sempre mascaram
    if (b.length < off + 4 + len) return;
    const mask = b.subarray(off, off + 4), payload = Buffer.from(b.subarray(off + 4, off + 4 + len));
    for (let i = 0; i < len; i++) payload[i] ^= mask[i & 3];
    c.buf = b.subarray(off + 4 + len);
    c.seen = Date.now();
    if (op === 8) { wsCtl(c, 8); return c.sock.end(); }
    if (op === 9) { wsCtl(c, 10, payload.subarray(0, 100)); continue; }
    if (op === 10) continue;
    if (op === 1 || op === 0) {
      c.frag = op === 1 ? [payload] : (c.frag || []).concat([payload]);
      if (c.frag.reduce((s, x) => s + x.length, 0) > 8192) return c.sock.destroy();
      if (fin) { const txt = Buffer.concat(c.frag).toString('utf8'); c.frag = null; handle(c, txt); }
    }
  }
}

// ---------- utilidades ----------
const num = (v, a, b, d) => { v = Number(v); return Number.isFinite(v) ? Math.max(a, Math.min(b, v)) : d; };
function cleanName(s) { s = String(s || '').replace(/[^\p{L}\p{N} _\-]/gu, '').trim().slice(0, 12); return s || 'Ladrão'; }
function cleanRoom(s) { return String(s || '').toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 6); }
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
function inRoom(c) { return c.room && rooms.get(c.room); }
function bcast(room, obj, except) { for (const p of room.players.values()) if (p !== except) wsSend(p, obj); }
function tuple(p) { return [p.id, Math.round(p.x), Math.round(p.y), p.f, +p.h.toFixed(2), p.d, p.v, p.c, p.s]; }
function rosterOf(room) {
  return [...room.players.values()].map(p => ({ id: p.id, n: p.name, c: Math.floor(p.coins), s: p.stolen, l: p.level, pen: p.pen, hue: p.hue }));
}
function topList() {
  return [...globalTop.values()].sort((a, b) => b.s - a.s || b.c - a.c).slice(0, 10);
}
function sendRoster(room) { bcast(room, { t: 'ros', p: rosterOf(room) }); room.rosterDirty = false; }

function joinRoom(c, want) {
  leaveRoom(c);
  let code = cleanRoom(want), room;
  if (!code) {                                   // sala pública: primeira com vaga
    for (let i = 1; ; i++) {
      code = 'PUBLICA' + (i > 1 ? i : '');
      room = rooms.get(code);
      if (!room || room.players.size < MAX_ROOM) break;
    }
  } else { room = rooms.get(code); if (room && room.players.size >= MAX_ROOM) return wsSend(c, { t: 'err', m: 'Sala cheia (' + MAX_ROOM + ').' }); }
  if (!room) {
    if (rooms.size >= MAX_ROOMS) return wsSend(c, { t: 'err', m: 'Servidor cheio, tente mais tarde.' });
    room = { code, players: new Map(), rosterDirty: false }; rooms.set(code, room);
  }
  c.room = code; room.players.set(c.id, c);
  wsSend(c, { t: 'joined', id: c.id, room: code, pub: code.startsWith('PUBLICA'), max: MAX_ROOM });
  wsSend(c, { t: 'st', p: [...room.players.values()].filter(p => p !== c).map(tuple) });
  wsSend(c, { t: 'top', g: topList() });
  bcast(room, { t: 'msg', m: '👋 ' + c.name + ' entrou na sala' }, c);
  sendRoster(room);
}
function leaveRoom(c) {
  const room = inRoom(c); if (!room) { c.room = null; return; }
  room.players.delete(c.id); c.room = null;
  if (!room.players.size) rooms.delete(room.code);
  else { bcast(room, { t: 'gone', id: c.id }); bcast(room, { t: 'msg', m: '🚪 ' + c.name + ' saiu' }); sendRoster(room); }
}

// ---------- mensagens ----------
function handle(c, txt) {
  const now = Date.now();
  if (now - c.win > 1000) { c.win = now; c.cnt = 0; }
  if (++c.cnt > 40) return;                      // anti-flood
  let m; try { m = JSON.parse(txt); } catch (e) { return; }
  if (!m || typeof m.t !== 'string') return;
  if (m.t === 'join') {
    c.name = cleanName(m.name); c.uid = String(m.uid || '').slice(0, 40) || ('x' + c.id);
    c.hue = num(m.hue, 0, 360, 0) | 0;
    return joinRoom(c, m.room);
  }
  if (m.t === 'ping') return wsSend(c, { t: 'pong' });
  const room = inRoom(c); if (!room) return;
  if (m.t === 'pos') {
    c.x = num(m.x, 0, 1400, c.x); c.y = num(m.y, 0, 4500, c.y); c.f = m.f < 0 ? -1 : 1; c.h = num(m.h, 0, 6, 0);
    c.d = m.d ? 1 : 0; c.v = m.v === 's' || m.v === 'm' ? m.v : ''; c.c = num(m.c, -1, 4, -1) | 0; c.s = num(m.s, 0, 3, 0) | 0;
    c.dirty = true;
  } else if (m.t === 'stat') {
    c.coins = num(m.c, 0, 1e12, 0); c.stolen = num(m.s, 0, 1e9, 0) | 0; c.level = num(m.l, 1, 9999, 1) | 0;
    if (Array.isArray(m.pen)) c.pen = [0, 1, 2, 3, 4].map(i => num(m.pen[i], 0, 80, 0) | 0);
    globalTop.set(c.uid, { n: c.name, s: c.stolen, c: Math.floor(c.coins), l: c.level }); scoresDirty = true;
    room.rosterDirty = true;
  } else if (m.t === 'raid') raid(c, room, room.players.get(num(m.to, 0, 1e9, -1) | 0));
  else if (m.t === 'tackle') tackle(c, room, room.players.get(num(m.to, 0, 1e9, -1) | 0));
}
function raid(c, room, v) {
  const now = Date.now();
  const fail = r => wsSend(c, { t: 'raidfail', m: r });
  if (!v || v === c) return fail('Jogador não encontrado.');
  if (c.y < PEN_TOP || c.y > PEN_BOTTOM) return fail('Entre no cercado para assaltar!');
  const wait = Math.ceil((c.lastRaid + RAID_COOLDOWN - now) / 1000);
  if (wait > 0) return fail('Espere ' + wait + 's para assaltar de novo.');
  if (now < v.immuneUntil) return fail(v.name + ' está protegido por um tempo.');
  const total = v.pen.reduce((a, b) => a + b, 0);
  if (!total) return fail('O cercado de ' + v.name + ' está vazio.');
  c.lastRaid = now;
  // dono por perto, dentro do cercado: pega em flagrante
  if (v.y >= PEN_TOP && v.y <= PEN_BOTTOM && dist(c, v) < RAID_GUARD_DIST) {
    wsSend(c, { t: 'caught', by: v.name });
    wsSend(v, { t: 'msg', m: '🛡️ Você pegou ' + c.name + ' tentando assaltar seu cercado!' });
    return fail(v.name + ' te pegou em flagrante!');
  }
  let k = Math.floor(Math.random() * total), rar = 0;
  for (; rar < 5; rar++) { if (k < v.pen[rar]) break; k -= v.pen[rar]; }
  v.pen[rar]--; c.pen[rar] = Math.min(80, c.pen[rar] + 1); v.immuneUntil = now + RAID_IMMUNE;
  wsSend(v, { t: 'robbed', rar, by: c.name, kind: 'pen' });
  wsSend(c, { t: 'raidok', rar, from: v.name });
  bcast(room, { t: 'msg', m: '🏴‍☠️ ' + c.name + ' assaltou o cercado de ' + v.name + '!' });
  room.rosterDirty = true;
}
function tackle(c, room, v) {
  const now = Date.now();
  if (!v || v === c || c.c >= 0 || v.c < 0) return;
  if (now - c.lastTackle < TACKLE_COOLDOWN || now < v.tackleImmune) return;
  if (dist(c, v) > TACKLE_DIST) return;
  c.lastTackle = now; v.tackleImmune = now + TACKLE_IMMUNE;
  const rar = v.c; v.c = -1; c.c = rar;
  wsSend(v, { t: 'tackled', by: c.name });
  wsSend(c, { t: 'tackleok', rar, from: v.name });
  bcast(room, { t: 'msg', m: '💥 ' + c.name + ' roubou o Posei que ' + v.name + ' carregava!' });
}

// ---------- ticks ----------
setInterval(() => {            // estados (10x/s): só quem mudou
  for (const room of rooms.values()) {
    if (room.players.size < 2) { for (const p of room.players.values()) p.dirty = false; continue; }
    const d = []; for (const p of room.players.values()) if (p.dirty) { d.push(tuple(p)); p.dirty = false; }
    if (d.length) bcast(room, { t: 'st', p: d });
  }
}, 100);
setInterval(() => {            // placar da sala (1x/s se mudou) e limpeza de conexões mortas
  const now = Date.now();
  for (const room of rooms.values()) if (room.rosterDirty) sendRoster(room);
  for (const room of rooms.values()) for (const p of [...room.players.values()]) if (now - p.seen > 70000) p.sock.destroy();
}, 1000);
setInterval(() => {            // placar global (10s)
  const g = topList();
  for (const room of rooms.values()) bcast(room, { t: 'top', g });
  if (scoresDirty) { scoresDirty = false; try { fs.writeFileSync(SCORES_FILE, JSON.stringify(Object.fromEntries(globalTop))); } catch (e) {} }
}, 10000);

// ---------- HTTP + upgrade ----------
const server = http.createServer((req, res) => {
  if (req.url === '/status') {
    res.writeHead(200, { 'content-type': 'application/json', 'access-control-allow-origin': '*' });
    return res.end(JSON.stringify({ ok: true, rooms: rooms.size, players: conns }));
  }
  res.writeHead(200, { 'content-type': 'text/plain; charset=utf-8' });
  res.end('Roube el Posei - servidor multiplayer OK\n');
});
server.on('upgrade', (req, sock) => {
  const key = req.headers['sec-websocket-key'];
  if (!key || String(req.headers.upgrade).toLowerCase() !== 'websocket' || conns >= MAX_CONN) return sock.destroy();
  const acc = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
  sock.setNoDelay(true);
  conns++;
  const c = { id: nextId++, sock, buf: Buffer.alloc(0), seen: Date.now(), win: 0, cnt: 0, room: null, name: 'Ladrão', uid: '', hue: 0,
    x: 700, y: 2600, f: 1, h: 0, d: 0, v: '', c: -1, s: 0, dirty: false, coins: 0, stolen: 0, level: 1, pen: [0, 0, 0, 0, 0],
    lastRaid: 0, immuneUntil: 0, lastTackle: 0, tackleImmune: 0 };
  sock.on('data', d => { try { onData(c, d); } catch (e) { sock.destroy(); } });
  sock.on('close', () => { conns--; leaveRoom(c); });
  sock.on('error', () => {});
});
if (require.main === module) server.listen(PORT, () => console.log('Roube el Posei servidor na porta ' + PORT));
module.exports = { server };
