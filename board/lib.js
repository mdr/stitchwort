'use strict';
// Data layer for the kanban board: reads and writes board/tickets.json.
// Standard library only. Used by the CLI (board/board) and the server.
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');
const links = require('./links');

const STATUSES = ['backlog', 'next', 'doing', 'review', 'done'];
const AGENTS = ['', 'Opus', 'Sonnet', 'DeepSeek', 'GLM', 'Matt', 'Claude'];
const KEY_ORDER = ['id', 'title', 'status', 'agent', 'where', 'labels', 'epic', 'body', 'created', 'updated', 'commits'];
const EPIC_STATUSES = ['active', 'paused', 'waiting-on-matt', 'done'];

const defaultFile = () => process.env.BOARD_FILE || path.join(__dirname, 'tickets.json');
const today = () => new Date().toISOString().slice(0, 10);
const sleep = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);

class BoardError extends Error {}

function normalizeTicket(t) {
  const out = {};
  for (const k of KEY_ORDER) {
    if (k === 'epic') {
      // Left out when empty, so untagged tickets keep their old shape in the file.
      if (t.epic) out.epic = String(t.epic);
    } else if (k === 'labels' || k === 'commits') out[k] = Array.isArray(t[k]) ? t[k].map(String) : [];
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

// Epics: board/epics.json next to the board file (see board/README.md).
const epicsFile = (file = defaultFile()) => path.join(path.dirname(file), 'epics.json');

function loadEpics(file = defaultFile()) {
  const ef = epicsFile(file);
  let text;
  try {
    text = fs.readFileSync(ef, 'utf8');
  } catch (e) {
    if (e.code === 'ENOENT') return [];
    throw e;
  }
  let data;
  try {
    data = JSON.parse(text);
  } catch (e) {
    throw new BoardError(`${ef} is not valid JSON: ${e.message}`);
  }
  const list = (x) => (Array.isArray(x) ? x.map(String) : []);
  return (data.epics || []).map((e) => {
    if (!e.id || !/^[a-z0-9][a-z0-9-]*$/.test(e.id)) throw new BoardError(`${ef}: bad epic id "${e.id}"`);
    if (!EPIC_STATUSES.includes(e.status)) throw new BoardError(`${ef}: epic ${e.id} has status "${e.status}" (one of: ${EPIC_STATUSES.join(', ')})`);
    return {
      id: e.id, title: String(e.title || e.id), goal: String(e.goal || ''), status: e.status,
      done: list(e.done), now: list(e.now), next: list(e.next), links: list(e.links),
    };
  });
}

function checkEpic(epic, file = defaultFile()) {
  if (epic === '') return '';
  const ids = loadEpics(file).map((e) => e.id);
  if (!ids.includes(epic)) throw new BoardError(`unknown epic "${epic}" (see board/epics.json; one of: ${ids.join(', ') || 'none defined'})`);
  return epic;
}

// Each epic with its ticket counts: open (not done) and done.
function epicSummaries(data, file = defaultFile()) {
  return loadEpics(file).map((e) => {
    const ts = data.tickets.filter((t) => t.epic === e.id);
    return { ...e, open: ts.filter((t) => t.status !== 'done').length, doneCount: ts.filter((t) => t.status === 'done').length };
  });
}

// Sets `epic` on tickets from a { "SW number": "epic id" } mapping without touching
// `updated`. Tickets that already have an epic are kept unless `force`.
// Returns { set, kept, missing } (numbers).
function applyEpics(mapping, { force = false } = {}, file = defaultFile()) {
  const known = new Set(loadEpics(file).map((e) => e.id));
  for (const [k, v] of Object.entries(mapping)) {
    parseId(k);
    if (!known.has(v)) throw new BoardError(`SW-${k}: unknown epic "${v}"`);
  }
  return update((data) => {
    const r = { set: [], kept: [], missing: [] };
    for (const [k, v] of Object.entries(mapping)) {
      const t = data.tickets.find((x) => x.id === parseId(k));
      if (!t) r.missing.push(parseId(k));
      else if (t.epic && t.epic !== v && !force) r.kept.push(t.id);
      else { if (t.epic !== v) r.set.push(t.id); t.epic = v; }
    }
    return r;
  }, file);
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
function applyFields(t, fields, file) {
  if ('title' in fields && !String(fields.title).trim()) throw new BoardError('title must not be empty');
  if ('status' in fields) checkStatus(fields.status);
  if ('agent' in fields) checkAgent(fields.agent);
  if ('epic' in fields) checkEpic(String(fields.epic), file);
  if ('title' in fields) t.title = String(fields.title).trim();
  if ('status' in fields) t.status = fields.status;
  if ('agent' in fields) t.agent = fields.agent;
  if ('where' in fields) t.where = String(fields.where);
  if ('body' in fields) t.body = String(fields.body);
  if ('epic' in fields) { if (fields.epic) t.epic = String(fields.epic); else delete t.epic; }
  if ('labels' in fields) t.labels = cleanList(fields.labels);
  if ('commits' in fields) t.commits = cleanList(fields.commits);
  t.updated = today();
}

function addTicket(data, fields, file) {
  const t = normalizeTicket({ id: data.next, status: 'backlog', created: today(), updated: today() });
  applyFields(t, { title: '', ...fields }, file);
  data.next += 1;
  data.tickets.push(t);
  data.tickets.sort((a, b) => a.id - b.id);
  return t;
}

function editTicket(data, id, fields, file) {
  const t = find(data, id);
  applyFields(t, fields, file);
  return t;
}

function removeTicket(data, id) {
  const t = find(data, id);
  data.tickets = data.tickets.filter((x) => x.id !== id);
  return t; // data.next is untouched: numbers are never reused
}

// Documents: git-tracked files under the repo root that the server shows at /doc/<path>.
const repoRoot = () => path.resolve(__dirname, '..');

// The set of git-tracked paths (repo-relative, '/'-separated).
function trackedFiles(root = repoRoot()) {
  const out = execFileSync('git', ['ls-files', '-z'], { cwd: root, maxBuffer: 1 << 28 });
  return new Set(out.toString('utf8').split('\0').filter(Boolean));
}

// Maps a requested path to { abs, kind } if it is a tracked, servable document, else
// null. Refuses anything not already in normal form (`..`, `.`, `//`, a leading `/`,
// backslashes, NUL), anything untracked, and symlinks that leave the repo.
function resolveDoc(root, rel, tracked) {
  if (typeof rel !== 'string' || !rel || rel.includes('\0') || rel.includes('\\') || rel.startsWith('/')) return null;
  if (rel.split('/').some((seg) => seg === '' || seg === '.' || seg === '..')) return null;
  if (!tracked.has(rel)) return null;
  const kind = links.docKind(rel);
  if (!kind) return null;
  const abs = path.join(root, rel);
  try {
    const real = fs.realpathSync(abs);
    const base = fs.realpathSync(root);
    if (real !== base && !real.startsWith(base + path.sep)) return null;
    if (!fs.statSync(real).isFile()) return null;
  } catch (_) {
    return null;
  }
  return { abs, kind };
}

// First `# ` heading of a markdown file, or '' (for labels in lists).
function docTitle(root, rel) {
  try {
    const head = fs.readFileSync(path.join(root, rel), 'utf8').slice(0, 4000);
    const m = /^#\s+(.+?)\s*#*\s*$/m.exec(head);
    return m ? m[1] : '';
  } catch (_) {
    return '';
  }
}

// docs/reviews/SW-N-topic.md files whose ticket number is in `ticketIds`.
function reviewDocs(tracked, ticketIds) {
  const out = [];
  for (const p of tracked) {
    const m = /^docs\/reviews\/SW-(\d+)-[^/]+\.md$/.exec(p);
    if (m && ticketIds.has(Number(m[1]))) out.push(p);
  }
  return out.sort();
}

// For the epic cards: `docs` (the epic's `links` that are documents, plus the review
// files of its tickets, live or archived) and `links` (the rest of its links).
function epicDocs(epic, tickets, tracked, root = repoRoot(), file = defaultFile()) {
  const isDoc = (l) => {
    const m = /^([^:]+?)(?::\d+)?$/.exec(l);
    return !!m && tracked.has(m[1]) && !!links.docKind(m[1]);
  };
  const linkDocs = epic.links.filter(isDoc).map((l) => l.replace(/:\d+$/, ''));
  const hasReviews = [...tracked].some((p) => p.startsWith('docs/reviews/SW-'));
  let reviews = [];
  if (hasReviews) {
    const ids = new Set(tickets.filter((t) => t.epic === epic.id).map((t) => t.id));
    for (const t of loadArchived(file)) if (t.epic === epic.id) ids.add(t.id);
    reviews = reviewDocs(tracked, ids);
  }
  const paths = [...new Set([...linkDocs, ...reviews])];
  return {
    docs: paths.map((p) => ({ path: p, title: docTitle(root, p), review: reviews.includes(p) })),
    links: epic.links.filter((l) => !isDoc(l)),
  };
}

module.exports = {
  STATUSES, AGENTS, BoardError, defaultFile, load, save, serialize, update, find, parseId,
  addTicket, editTicket, removeTicket, normalizeTicket, today,
  archiveDir, loadArchived, findArchived, archiveBefore,
  repoRoot, trackedFiles, resolveDoc, docTitle, reviewDocs, epicDocs,
  EPIC_STATUSES, epicsFile, loadEpics, checkEpic, epicSummaries, applyEpics,
};
