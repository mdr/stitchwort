'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync, spawn } = require('child_process');
const lib = require('./lib');

const CLI = path.join(__dirname, 'board');

function tmpFile() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'board-test-'));
  return path.join(dir, 'tickets.json');
}

function cli(file, ...args) {
  const r = spawnSync(process.execPath, [CLI, ...args], { env: { ...process.env, BOARD_FILE: file }, encoding: 'utf8' });
  return { code: r.status, out: r.stdout.trim(), err: r.stderr.trim() };
}

test('add numbers tickets from 1 and prints the id', () => {
  const f = tmpFile();
  assert.equal(cli(f, 'add', 'first').out, 'SW-1');
  assert.equal(cli(f, 'add', 'second', '--status', 'next', '--label', 'a', '--label', 'b', '--body', 'text').out, 'SW-2');
  const d = lib.load(f);
  assert.equal(d.next, 3);
  assert.deepEqual(d.tickets.map((t) => t.id), [1, 2]);
  assert.equal(d.tickets[1].status, 'next');
  assert.deepEqual(d.tickets[1].labels, ['a', 'b']);
  assert.equal(d.tickets[1].body, 'text');
  assert.equal(d.tickets[0].status, 'backlog');
});

test('numbers are never reused after rm', () => {
  const f = tmpFile();
  cli(f, 'add', 'one');
  cli(f, 'add', 'two');
  assert.equal(cli(f, 'rm', 'SW-2').code, 0);
  assert.equal(cli(f, 'add', 'three').out, 'SW-3');
  cli(f, 'rm', '1');
  cli(f, 'rm', '3');
  assert.equal(cli(f, 'add', 'four').out, 'SW-4');
  assert.deepEqual(lib.load(f).tickets.map((t) => t.id), [4]);
});

test('next is raised above the largest id if the file is edited by hand', () => {
  const f = tmpFile();
  fs.writeFileSync(f, JSON.stringify({ next: 1, tickets: [{ id: 7, title: 'x', status: 'next' }] }));
  assert.equal(cli(f, 'add', 'y').out, 'SW-8');
});

test('move, assign, unassign, edit, commit', () => {
  const f = tmpFile();
  cli(f, 'add', 'work');
  assert.equal(cli(f, 'move', '1', 'review').code, 0);
  assert.equal(lib.load(f).tickets[0].status, 'review');
  cli(f, 'move', '1', 'next');
  assert.equal(cli(f, 'assign', '1', 'Sonnet', '--where', '/tmp/wt').code, 0);
  let t = lib.load(f).tickets[0];
  assert.deepEqual([t.agent, t.where, t.status], ['Sonnet', '/tmp/wt', 'doing']);
  cli(f, 'unassign', '1');
  t = lib.load(f).tickets[0];
  assert.deepEqual([t.agent, t.where, t.status], ['', '', 'doing']);
  cli(f, 'edit', '1', '--title', 'renamed', '--label', 'x', '--add-label', 'y', '--add-label', 'x', '--body', 'b');
  t = lib.load(f).tickets[0];
  assert.deepEqual([t.title, t.labels, t.body], ['renamed', ['x', 'y'], 'b']);
  cli(f, 'edit', '1', '--rm-label', 'x');
  assert.deepEqual(lib.load(f).tickets[0].labels, ['y']);
  cli(f, 'commit', '1', 'abc1234');
  cli(f, 'commit', '1', 'def5678');
  assert.deepEqual(lib.load(f).tickets[0].commits, ['abc1234', 'def5678']);
});

test('body-file reads a file', () => {
  const f = tmpFile();
  const bf = path.join(path.dirname(f), 'body.md');
  fs.writeFileSync(bf, '# Heading\n\nline two\n');
  cli(f, 'add', 't', '--body-file', bf);
  assert.equal(lib.load(f).tickets[0].body, '# Heading\n\nline two\n');
});

test('list filters and show', () => {
  const f = tmpFile();
  cli(f, 'add', 'a', '--status', 'doing', '--agent', 'Opus', '--label', 'k');
  cli(f, 'add', 'b', '--status', 'doing', '--agent', 'GLM');
  cli(f, 'add', 'c');
  assert.equal(cli(f, 'list', '--status', 'doing').out.split('\n').length, 2);
  assert.match(cli(f, 'list', '--agent', 'GLM').out, /SW-2 .*b/);
  assert.match(cli(f, 'list', '--label', 'k').out, /SW-1/);
  assert.equal(JSON.parse(cli(f, 'show', '3', '--json').out).title, 'c');
  assert.match(cli(f, 'show', 'SW-1').out, /status:  doing/);
});

test('errors are clear and exit non-zero without changing the file', () => {
  const f = tmpFile();
  cli(f, 'add', 'a');
  const before = fs.readFileSync(f, 'utf8');
  for (const args of [
    ['move', '1', 'bogus'], ['move', '9', 'done'], ['assign', '1', 'Gemini'], ['show', 'x'], ['rm', '5'],
    ['add'], ['add', ''], ['edit', '1'], ['nonsense'], ['add', 't', '--bogus', 'x'], ['list', '--status', 'nope'],
  ]) {
    const r = cli(f, ...args);
    assert.notEqual(r.code, 0, args.join(' '));
    assert.match(r.err, /^board: /, args.join(' '));
  }
  assert.equal(fs.readFileSync(f, 'utf8'), before);
});

test('the file is pretty-printed, key-ordered and sorted by number', () => {
  const f = tmpFile();
  fs.writeFileSync(f, JSON.stringify({ next: 5, tickets: [{ title: 'b', id: 3 }, { id: 1, title: 'a', extra: 1 }] }));
  cli(f, 'edit', '1', '--body', 'hi');
  const text = fs.readFileSync(f, 'utf8');
  assert.ok(text.endsWith('}\n'));
  const d = JSON.parse(text);
  assert.deepEqual(d.tickets.map((t) => t.id), [1, 3]);
  assert.deepEqual(Object.keys(d.tickets[0]), ['id', 'title', 'status', 'agent', 'where', 'labels', 'body', 'created', 'updated', 'commits']);
  assert.match(text, /^{\n  "next": 5,\n  "tickets": \[\n    {\n      "id": 1,/);
});

test('writes are atomic: no temp files left, and a failed write keeps the old file', () => {
  const f = tmpFile();
  cli(f, 'add', 'a');
  assert.deepEqual(fs.readdirSync(path.dirname(f)).sort(), ['tickets.json']);
  // An exception inside update() must not touch the file or leave the lock.
  const before = fs.readFileSync(f, 'utf8');
  assert.throws(() => lib.update((d) => { d.next = 99; throw new Error('boom'); }, f), /boom/);
  assert.equal(fs.readFileSync(f, 'utf8'), before);
  assert.deepEqual(fs.readdirSync(path.dirname(f)).sort(), ['tickets.json']);
  // save() goes through a rename: a reader never sees a partial file.
  const big = { next: 2, tickets: [{ id: 1, title: 'x', body: 'y'.repeat(2e6) }] };
  lib.save(big, f);
  assert.equal(JSON.parse(fs.readFileSync(f, 'utf8')).tickets[0].body.length, 2e6);
});

test('a change made elsewhere is re-read before every write', () => {
  const f = tmpFile();
  cli(f, 'add', 'one');
  // Another writer (the server, say) adds a ticket between our load and our update.
  const stale = lib.load(f);
  lib.update((d) => lib.addTicket(d, { title: 'by someone else' }), f);
  assert.equal(stale.tickets.length, 1);
  lib.update((d) => lib.addTicket(d, { title: 'by us' }), f);
  const d = lib.load(f);
  assert.deepEqual(d.tickets.map((t) => t.title), ['one', 'by someone else', 'by us']);
  assert.deepEqual(d.tickets.map((t) => t.id), [1, 2, 3]);
});

test('concurrent CLI processes do not lose updates or reuse numbers', async () => {
  const f = tmpFile();
  const runs = Array.from({ length: 12 }, (_, i) => new Promise((resolve) => {
    const p = spawn(process.execPath, [CLI, 'add', `t${i}`], { env: { ...process.env, BOARD_FILE: f } });
    let out = '';
    p.stdout.on('data', (c) => { out += c; });
    p.on('close', (code) => resolve({ code, out: out.trim() }));
  }));
  const results = await Promise.all(runs);
  assert.ok(results.every((r) => r.code === 0));
  const ids = results.map((r) => r.out).sort();
  assert.equal(new Set(ids).size, 12);
  const d = lib.load(f);
  assert.equal(d.tickets.length, 12);
  assert.equal(d.next, 13);
});

test('a stale lock directory is ignored', () => {
  const f = tmpFile();
  cli(f, 'add', 'a');
  fs.mkdirSync(`${f}.lock`);
  const old = new Date(Date.now() - 60000);
  fs.utimesSync(`${f}.lock`, old, old);
  assert.equal(cli(f, 'add', 'b').out, 'SW-2');
});

test('the migrated board file is well-formed', () => {
  const d = lib.load(path.join(__dirname, 'tickets.json'));
  const ids = d.tickets.map((t) => t.id);
  assert.equal(new Set(ids).size, ids.length);
  assert.ok(d.next > Math.max(...ids));
  for (const t of d.tickets) {
    assert.ok(lib.STATUSES.includes(t.status), `SW-${t.id}`);
    assert.ok(lib.AGENTS.includes(t.agent), `SW-${t.id}`);
    assert.ok(t.title, `SW-${t.id}`);
  }
  assert.equal(fs.readFileSync(path.join(__dirname, 'tickets.json'), 'utf8'), lib.serialize(d));
});
