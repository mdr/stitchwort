'use strict';
// Data layer for the kanban board: reads and writes board/tickets.json.
// Standard library only. Used by the CLI (board/board) and the server.
const fs = require('fs');
const path = require('path');

const STATUSES = ['backlog', 'next', 'doing', 'review', 'done'];
const AGENTS = ['', 'Opus', 'Sonnet', 'DeepSeek', 'GLM', 'Matt', 'Claude'];
const KEY_ORDER = ['id', 'title', 'status', 'agent', 'where', 'labels', 'body', 'created', 'updated', 'commits'];

const defaultFile = () => process.env.BOARD_FILE || path.join(__dirname, 'tickets.json');
const today = () => new Date().toISOString().slice(0, 10);
const sleep = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);

class BoardError extends Error {}

function normalizeTicket(t) {
  const out = {};
  for (const k of KEY_ORDER) {
    if (k === 'labels' || k === 'commits') out[k] = Array.isArray(t[k]) ? t[k].map(String) : [];
    else if (k === 'id') out[k] = t[k];
    else out[k] = t[k] == null ? '' : String(t[k]);
  }
  return out;
}

function parseId(s) {
  const m = /^(?:SW-)?(\d+)$/i.exec(String(s).trim());
  if (!m) throw new BoardError(`not a ticket number: ${s}`);
  return Number(m[1]);
}

function load(file = defaultFile()) {
  let text;
  try {
    text = fs.readFileSync(file, 'utf8');
  } catch (e) {
    if (e.code === 'ENOENT') return { next: 1, tickets: [] };
    throw e;
  }
  let data;
  try {
    data = JSON.parse(text);
  } catch (e) {
    throw new BoardError(`${file} is not valid JSON: ${e.message}`);
  }
  const tickets = (data.tickets || []).map(normalizeTicket);
  const maxId = tickets.reduce((m, t) => Math.max(m, t.id), 0);
  return { next: Math.max(Number(data.next) || 1, maxId + 1), tickets };
}

function serialize(data) {
  const tickets = data.tickets.map(normalizeTicket).sort((a, b) => a.id - b.id);
  return JSON.stringify({ next: data.next, tickets }, null, 2) + '\n';
}

// Atomic: write a temp file in the same directory, then rename over the target.
function save(data, file = defaultFile()) {
  const tmp = `${file}.${process.pid}.${Date.now()}.tmp`;
  fs.writeFileSync(tmp, serialize(data));
  fs.renameSync(tmp, file);
}

// A directory lock, so two writers do not interleave read-modify-write.
function withLock(file, fn) {
  const lock = `${file}.lock`;
  const start = Date.now();
  for (;;) {
    try {
      fs.mkdirSync(lock);
      break;
    } catch (e) {
      if (e.code !== 'EEXIST') throw e;
      try {
        if (Date.now() - fs.statSync(lock).mtimeMs > 10000) fs.rmdirSync(lock); // stale
      } catch (_) { /* released meanwhile */ }
      if (Date.now() - start > 15000) throw new BoardError('timed out waiting for the board lock');
      sleep(20);
    }
  }
  try {
    return fn();
  } finally {
    try { fs.rmdirSync(lock); } catch (_) { /* already gone */ }
  }
}

// Re-reads the file, applies `fn(data)` (which mutates it), writes atomically.
function update(fn, file = defaultFile()) {
  return withLock(file, () => {
    const data = load(file);
    let result;
    try {
      result = fn(data);
    } catch (e) {
      const m = e instanceof BoardError && /^no ticket SW-(\d+)$/.exec(e.message);
      if (m && findArchived(Number(m[1]), file)) throw new BoardError(`SW-${m[1]} is archived (read-only)`);
      throw e;
    }
    save(data, file);
    return result;
  });
}

// Archive: old done tickets live in archive/YYYY-MM.json next to the board file
// (by the month of their `updated` date), in the same ticket format. The board
// file's `next` is never lowered, so archived numbers are not reused.
const archiveDir = (file = defaultFile()) => path.join(path.dirname(file), 'archive');

function archiveFiles(file) {
  const dir = archiveDir(file);
  let names;
  try {
    names = fs.readdirSync(dir);
  } catch (e) {
    if (e.code === 'ENOENT') return [];
    throw e;
  }
  return names.filter((n) => /^\d{4}-\d{2}\.json$/.test(n)).sort().map((n) => path.join(dir, n));
}

function loadArchiveFile(file) {
  let text;
  try {
    text = fs.readFileSync(file, 'utf8');
  } catch (e) {
    if (e.code === 'ENOENT') return [];
    throw e;
  }
  try {
    return (JSON.parse(text).tickets || []).map(normalizeTicket);
  } catch (e) {
    throw new BoardError(`${file} is not valid JSON: ${e.message}`);
  }
}

function loadArchived(file = defaultFile()) {
  return archiveFiles(file).flatMap(loadArchiveFile).sort((a, b) => a.id - b.id);
}

function findArchived(id, file = defaultFile()) {
  return loadArchived(file).find((t) => t.id === id) || null;
}

const DATE = /^\d{4}-\d{2}-\d{2}$/;

// Moves every done ticket updated before `before` (YYYY-MM-DD) from the board
// file into the archive. Returns the archived tickets. The archive files are
// written before the board file, so a crash can duplicate a ticket (the next
// run removes it from the board) but never lose one.
function archiveBefore(before, file = defaultFile()) {
  if (!DATE.test(before)) throw new BoardError(`not a date (YYYY-MM-DD): ${before}`);
  return withLock(file, () => {
    const data = load(file);
    const old = data.tickets.filter((t) => t.status === 'done' && t.updated < before);
    const months = {};
    for (const t of old) (months[t.updated.slice(0, 7)] ||= []).push(t);
    for (const [month, ts] of Object.entries(months)) {
      const target = path.join(archiveDir(file), `${month}.json`);
      const ids = new Set(ts.map((t) => t.id));
      const merged = loadArchiveFile(target).filter((t) => !ids.has(t.id)).concat(ts).sort((a, b) => a.id - b.id);
      fs.mkdirSync(archiveDir(file), { recursive: true });
      const tmp = `${target}.${process.pid}.${Date.now()}.tmp`;
      fs.writeFileSync(tmp, JSON.stringify({ tickets: merged }, null, 2) + '\n');
      fs.renameSync(tmp, target);
    }
    data.tickets = data.tickets.filter((t) => !old.includes(t));
    save(data, file);
    return old;
  });
}

function find(data, id) {
  const t = data.tickets.find((x) => x.id === id);
  if (!t) throw new BoardError(`no ticket SW-${id}`);
  return t;
}

function checkStatus(s) {
  if (!STATUSES.includes(s)) throw new BoardError(`unknown status "${s}" (one of: ${STATUSES.join(', ')})`);
  return s;
}

function checkAgent(a) {
  if (!AGENTS.includes(a)) throw new BoardError(`unknown agent "${a}" (one of: ${AGENTS.filter(Boolean).join(', ')})`);
  return a;
}

const cleanList = (xs) => [...new Set(xs.map((x) => String(x).trim()).filter(Boolean))];

// Applies the editable fields present in `fields` to ticket `t` (validating all first).
function applyFields(t, fields) {
  if ('title' in fields && !String(fields.title).trim()) throw new BoardError('title must not be empty');
  if ('status' in fields) checkStatus(fields.status);
  if ('agent' in fields) checkAgent(fields.agent);
  if ('title' in fields) t.title = String(fields.title).trim();
  if ('status' in fields) t.status = fields.status;
  if ('agent' in fields) t.agent = fields.agent;
  if ('where' in fields) t.where = String(fields.where);
  if ('body' in fields) t.body = String(fields.body);
  if ('labels' in fields) t.labels = cleanList(fields.labels);
  if ('commits' in fields) t.commits = cleanList(fields.commits);
  t.updated = today();
}

function addTicket(data, fields) {
  const t = normalizeTicket({ id: data.next, status: 'backlog', created: today(), updated: today() });
  applyFields(t, { title: '', ...fields });
  data.next += 1;
  data.tickets.push(t);
  data.tickets.sort((a, b) => a.id - b.id);
  return t;
}

function editTicket(data, id, fields) {
  const t = find(data, id);
  applyFields(t, fields);
  return t;
}

function removeTicket(data, id) {
  const t = find(data, id);
  data.tickets = data.tickets.filter((x) => x.id !== id);
  return t; // data.next is untouched: numbers are never reused
}

module.exports = {
  STATUSES, AGENTS, BoardError, defaultFile, load, save, serialize, update, find, parseId,
  addTicket, editTicket, removeTicket, normalizeTicket, today,
  archiveDir, loadArchived, findArchived, archiveBefore,
};
