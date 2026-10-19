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
    const result = fn(data);
    save(data, file);
    return result;
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
};
