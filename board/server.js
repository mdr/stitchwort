'use strict';
// Local web server for the kanban board: serves board/index.html and a JSON API
// on 127.0.0.1 only. Pushes a "changed" event (Server-Sent Events) when
// tickets.json changes on disk, whoever changed it.
const http = require('http');
const fs = require('fs');
const path = require('path');
const lib = require('./lib');

const HOST = '127.0.0.1';
const PORT = Number(process.env.PORT || 8020);
const FILE = lib.defaultFile();
const PAGE = path.join(__dirname, 'index.html');

const clients = new Set();
let lastStamp = '';

function stamp() {
  try {
    const s = fs.statSync(FILE);
    return `${s.mtimeMs}:${s.size}`;
  } catch (_) {
    return 'none';
  }
}

function broadcast() {
  const s = stamp();
  if (s === lastStamp) return;
  lastStamp = s;
  for (const res of clients) res.write(`event: changed\ndata: ${s}\n\n`);
}

let timer = null;
function scheduleBroadcast() {
  clearTimeout(timer);
  timer = setTimeout(broadcast, 50);
}

lastStamp = stamp();
try {
  fs.watch(path.dirname(FILE), (_event, name) => {
    if (!name || name === path.basename(FILE)) scheduleBroadcast();
  });
} catch (_) { /* polling below still covers it */ }
setInterval(broadcast, 2000).unref?.();
setInterval(() => { for (const res of clients) res.write(': keepalive\n\n'); }, 25000).unref?.();

function snapshot() {
  const d = lib.load(FILE);
  return { next: d.next, tickets: d.tickets, statuses: lib.STATUSES, agents: lib.AGENTS.filter(Boolean) };
}

function send(res, code, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
  res.end(body);
}

function readJson(req) {
  return new Promise((resolve, reject) => {
    let size = 0;
    const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size > 1e6) { reject(new lib.BoardError('request too large')); req.destroy(); }
      chunks.push(c);
    });
    req.on('end', () => {
      try {
        resolve(JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}'));
      } catch (_) {
        reject(new lib.BoardError('request body is not valid JSON'));
      }
    });
  });
}

const EDITABLE = ['title', 'status', 'agent', 'where', 'body', 'labels', 'commits'];
const pick = (o) => Object.fromEntries(EDITABLE.filter((k) => k in o).map((k) => [k, o[k]]));

async function api(req, res, url) {
  const m = /^\/api\/tickets(?:\/(\d+))?$/.exec(url.pathname);
  if (url.pathname === '/api/board' && req.method === 'GET') return send(res, 200, snapshot());
  if (!m) return send(res, 404, { error: 'not found' });
  if (req.method !== 'GET' && !String(req.headers['content-type'] || '').startsWith('application/json')) {
    return send(res, 415, { error: 'send application/json' });
  }
  const id = m[1] ? Number(m[1]) : null;
  if (req.method === 'POST' && id === null) {
    const fields = pick(await readJson(req));
    return send(res, 201, lib.update((d) => lib.addTicket(d, fields), FILE));
  }
  if (req.method === 'PATCH' && id !== null) {
    const fields = pick(await readJson(req));
    return send(res, 200, lib.update((d) => lib.editTicket(d, id, fields), FILE));
  }
  if (req.method === 'DELETE' && id !== null) {
    return send(res, 200, lib.update((d) => lib.removeTicket(d, id), FILE));
  }
  return send(res, 405, { error: 'method not allowed' });
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${HOST}:${PORT}`);
  // Refuse requests whose Host is not us (DNS rebinding).
  if (![`${HOST}:${PORT}`, `localhost:${PORT}`].includes(req.headers.host)) {
    res.writeHead(403);
    return res.end('forbidden');
  }
  try {
    if (url.pathname === '/' || url.pathname === '/index.html') {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
      return res.end(fs.readFileSync(PAGE));
    }
    if (url.pathname === '/api/events') {
      res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-store', Connection: 'keep-alive' });
      res.write('retry: 2000\n\n');
      clients.add(res);
      req.on('close', () => clients.delete(res));
      return;
    }
    if (url.pathname.startsWith('/api/')) return await api(req, res, url);
    res.writeHead(404);
    res.end('not found');
  } catch (e) {
    if (e instanceof lib.BoardError) return send(res, e.message.startsWith('no ticket') ? 404 : 400, { error: e.message });
    console.error(e);
    send(res, 500, { error: String(e.message || e) });
  }
});

server.listen(PORT, HOST, () => {
  console.log(`Kanban board: http://${HOST}:${PORT}/  (data: ${FILE})`);
});
