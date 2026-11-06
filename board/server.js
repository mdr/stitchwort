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
const ROOT = process.env.BOARD_ROOT || lib.repoRoot();
const STATIC = {
  '/links.js': ['links.js', 'text/javascript; charset=utf-8'],
  '/render.js': ['render.js', 'text/javascript; charset=utf-8'],
};

// git ls-files is cheap, but not worth running for every request.
let trackedCache = { at: 0, set: new Set() };
function tracked() {
  if (Date.now() - trackedCache.at > 3000) {
    try {
      trackedCache = { at: Date.now(), set: lib.trackedFiles(ROOT) };
    } catch (e) {
      console.error('git ls-files failed:', e.message);
      trackedCache = { at: Date.now(), set: new Set() };
    }
  }
  return trackedCache.set;
}

const clients = new Set();
let lastStamp = '';

function stamp() {
  const one = (f) => {
    try {
      const s = fs.statSync(f);
      return `${s.mtimeMs}:${s.size}`;
    } catch (_) {
      return 'none';
    }
  };
  return `${one(FILE)}|${one(lib.epicsFile(FILE))}`;
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
    if (!name || name === path.basename(FILE) || name === 'epics.json') scheduleBroadcast();
  });
} catch (_) { /* polling below still covers it */ }
setInterval(broadcast, 2000).unref?.();
setInterval(() => { for (const res of clients) res.write(': keepalive\n\n'); }, 25000).unref?.();

function snapshot() {
  const d = lib.load(FILE);
  let epics = [];
  try {
    const set = tracked();
    epics = lib.epicSummaries(d, FILE).map((e) => ({ ...e, ...lib.epicDocs(e, d.tickets, set, ROOT, FILE) }));
  } catch (e) {
    if (!(e instanceof lib.BoardError)) throw e; // a broken epics.json must not take the board down
  }
  return { next: d.next, tickets: d.tickets, statuses: lib.STATUSES, agents: lib.AGENTS.filter(Boolean), epics };
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

const EDITABLE = ['title', 'status', 'agent', 'where', 'epic', 'body', 'labels', 'commits'];
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
    return send(res, 201, lib.update((d) => lib.addTicket(d, fields, FILE), FILE));
  }
  if (req.method === 'PATCH' && id !== null) {
    const fields = pick(await readJson(req));
    return send(res, 200, lib.update((d) => lib.editTicket(d, id, fields, FILE), FILE));
  }
  if (req.method === 'DELETE' && id !== null) {
    return send(res, 200, lib.update((d) => lib.removeTicket(d, id), FILE));
  }
  return send(res, 405, { error: 'method not allowed' });
}

function serveDoc(_req, res, url) {
  let rel;
  try {
    rel = decodeURIComponent(url.pathname.slice('/doc/'.length));
  } catch (_) {
    rel = null;
  }
  const doc = rel && lib.resolveDoc(ROOT, rel, tracked());
  if (!doc) {
    res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
    return res.end('not a tracked document of this repository');
  }
  const headers = { 'Cache-Control': 'no-store', 'X-Content-Type-Options': 'nosniff' };
  if (url.searchParams.has('raw')) {
    res.writeHead(200, { ...headers, 'Content-Type': 'text/plain; charset=utf-8' });
    return res.end(fs.readFileSync(doc.abs));
  }
  res.writeHead(200, { ...headers, 'Content-Type': 'text/html; charset=utf-8' });
  res.end(fs.readFileSync(path.join(__dirname, 'doc.html')));
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
    if (STATIC[url.pathname]) {
      res.writeHead(200, { 'Content-Type': STATIC[url.pathname][1], 'Cache-Control': 'no-store' });
      return res.end(fs.readFileSync(path.join(__dirname, STATIC[url.pathname][0])));
    }
    if (url.pathname.startsWith('/doc/')) return serveDoc(req, res, url);
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
