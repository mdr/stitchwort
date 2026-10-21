'use strict';
// Run: node --test editors/vscode/test   (no dependencies)
// The fixture index was made with `stitchwort check --index index.json
// dot-notation.sw` run inside test/fixture; regenerate it if the format changes.
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const nav = require('../navindex');

const dir = path.join(__dirname, 'fixture');
const index = JSON.parse(fs.readFileSync(path.join(dir, 'index.json'), 'utf8'));
const lines = fs.readFileSync(path.join(dir, 'dot-notation.sw'), 'utf8').split('\n');
const file = nav.fileIndexByPath(index, 'dot-notation.sw');

// Position of the first occurrence of `word` on the 0-based `line`.
function at(line, word, skip = 0) {
  let col = lines[line].indexOf(word);
  for (let i = 0; i < skip; i++) col = lines[line].indexOf(word, col + 1);
  assert.ok(col >= 0, `${word} on line ${line}`);
  return [line, col];
}
function textAt(range) {
  assert.strictEqual(range[0], range[2]);
  return lines[range[0]].slice(range[1], range[3]);
}

test('file lookup', () => {
  assert.strictEqual(file, 0);
  assert.strictEqual(nav.fileIndexByPath(index, 'nope.sw'), -1);
});

test('every ref is found at its first and last character, over a name', () => {
  const mine = index.refs.filter((r) => r.file === file);
  assert.ok(mine.length > 50);
  for (const r of mine) {
    assert.ok(textAt(r.range).length > 0);
    assert.strictEqual(nav.refAt(index, file, r.range[0], r.range[1]), r);
    assert.strictEqual(nav.refAt(index, file, r.range[2], r.range[3] - 1), r);
  }
});

test('no ref in comments, blank space or other files', () => {
  assert.strictEqual(nav.refAt(index, file, 0, 3), null);
  assert.strictEqual(nav.refAt(index, file, 9999, 0), null);
  assert.strictEqual(nav.refAt(index, 1, 0, 0), null);
});

test('local variable goes to its binder', () => {
  // `| Put _ b => 1 + b.length`
  const [l, c] = at(10, 'b.length');
  const ref = nav.refAt(index, file, l, c);
  const t = nav.targetOf(index, ref);
  assert.strictEqual(t.path, 'dot-notation.sw');
  assert.strictEqual(t.std, null);
  assert.strictEqual(textAt(t.range), 'b');
  assert.strictEqual(t.range[0], 10);
  assert.notStrictEqual(t.range[1], c);
  assert.deepStrictEqual(nav.hoverOf(index, ref), { type: 'Bag a', name: 'b', kind: 'local' });
});

test('project declaration', () => {
  const [l, c] = at(26, 'Bag');
  const t = nav.targetOf(index, nav.refAt(index, file, l, c));
  assert.strictEqual(t.path, 'dot-notation.sw');
  assert.strictEqual(textAt(t.range), 'Bag');
});

test('standard library declaration carries std', () => {
  const ref = nav.refAt(index, file, ...at(20, 'toText'));
  const t = nav.targetOf(index, ref);
  assert.strictEqual(t.std, 'core.sw');
  assert.strictEqual(nav.hoverOf(index, ref).name, 'Std.Nat.toText');
});

test('dot notation points at the library function', () => {
  const ref = nav.refAt(index, file, ...at(28, 'length', 1));
  assert.deepStrictEqual(nav.hoverOf(index, ref), {
    type: 'Text -> Nat',
    name: 'Std.Text.length',
    kind: 'def',
  });
});

test('declaration site hovers via declAt', () => {
  const [l, c] = at(8, 'Bag.length');
  assert.strictEqual(nav.refAt(index, file, l, c), null);
  const d = nav.declAt(index, file, l, c + 5);
  assert.ok(d);
  assert.strictEqual(nav.hoverOf(index, d).kind, 'def');
  assert.strictEqual(nav.declAt(index, file, 0, 0), null);
});

test('outline nests constructors and fields under their type', () => {
  const roots = nav.outlineOf(index, file);
  const bag = roots.find((n) => n.name === 'Bag');
  assert.ok(bag);
  assert.deepStrictEqual(bag.children.map((c) => c.name), ['Empty', 'Put']);
  const person = roots.find((n) => n.name === 'Person');
  assert.deepStrictEqual(
    person.children.map((c) => [c.name, c.kind]),
    [
      ['name', 'field'],
      ['age', 'field'],
    ],
  );
  for (const n of roots) {
    for (const c of n.children) {
      assert.ok(nav.contains(n.fullRange, c.range[0], c.range[1]));
    }
  }
  assert.ok(roots.find((n) => n.name === 'showNat'));
  assert.deepStrictEqual(nav.outlineOf(index, 1), []);
});
