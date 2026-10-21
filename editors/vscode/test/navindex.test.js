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

test('a declaration has a ref at its own name, on the last component only', () => {
  const [l, c] = at(8, 'Bag.length');
  // `Bag.` is not part of the name range: `length` is.
  assert.strictEqual(nav.refAt(index, file, l, c), null);
  const ref = nav.refAt(index, file, l, c + 5);
  assert.ok(ref);
  assert.strictEqual(textAt(ref.range), 'length');
  assert.strictEqual(nav.hoverOf(index, ref).kind, 'def');
  assert.strictEqual(nav.hoverOf(index, ref).name, 'Main.Bag.length');
  const t = nav.targetOf(index, ref);
  assert.deepStrictEqual(t.range, ref.range);
});

test('references of a declaration: uses, with or without the declaration', () => {
  const ref = nav.refAt(index, file, ...at(10, 'length'));
  const withDecl = nav.referencesTo(index, ref, true);
  const without = nav.referencesTo(index, ref, false);
  assert.strictEqual(withDecl.length, without.length + 1);
  assert.deepStrictEqual(withDecl[0].range, [8, 8, 8, 14]);
  assert.deepStrictEqual(without.map((t) => t.range[0]), [10, 62]);
  for (const t of withDecl) {
    assert.strictEqual(t.path, 'dot-notation.sw');
    assert.strictEqual(textAt(t.range), 'length');
  }
  // the same answer from the declaration's own name
  const fromDecl = nav.refAt(index, file, ...at(8, 'length'));
  assert.deepStrictEqual(nav.referencesTo(index, fromDecl, true), withDecl);
});

test('references of a local variable include its binder only on request', () => {
  const ref = nav.refAt(index, file, ...at(10, 'b.length'));
  const without = nav.referencesTo(index, ref, false);
  assert.deepStrictEqual(without.map((t) => t.range[0]), [10]);
  const withDecl = nav.referencesTo(index, ref, true);
  assert.strictEqual(withDecl.length, 2);
  assert.strictEqual(textAt(withDecl[0].range), 'b');
  assert.ok(withDecl[0].range[1] < withDecl[1].range[1]);
});

test('references of a library function are in the project, and the library', () => {
  const ref = nav.refAt(index, file, ...at(28, 'length', 1));
  const refs = nav.referencesTo(index, ref, false);
  // `t.length` on line 28 and `p.name.length` on line 34: Text.length
  assert.ok(refs.some((t) => t.range[0] === 28 && t.path === 'dot-notation.sw'));
  assert.ok(refs.every((t) => t.std || t.path === 'dot-notation.sw'));
});

test('diagnostics by file', () => {
  assert.strictEqual(nav.diagnosticsByFile(index).size, 0);
  const bad = JSON.parse(fs.readFileSync(path.join(dir, 'errors.json'), 'utf8'));
  const byFile = nav.diagnosticsByFile(bad);
  assert.deepStrictEqual([...byFile.keys()], ['errors.sw']);
  const list = byFile.get('errors.sw');
  assert.deepStrictEqual(
    list.map((d) => [d.severity, d.code, d.range]),
    [
      ['error', 'E-TYPE-MISMATCH', [2, 16, 2, 22]],
      ['error', 'E-UNKNOWN-NAME', [6, 18, 6, 25]],
    ],
  );
  assert.strictEqual(
    list[0].message,
    'type mismatch\nexpected `Nat`, but this has type `Text`',
  );
});

test('diagnostics: warnings, notes and secondary labels; library files skipped', () => {
  const fake = {
    files: [{ path: 'a.sw' }, { path: 'b.sw' }, { path: 'x/core.sw', std: 'core.sw' }],
    diagnostics: [
      {
        severity: 'warning',
        code: 'W-X',
        message: 'm',
        file: 0,
        range: [0, 0, 0, 1],
        labels: [
          { file: 0, range: [0, 0, 0, 1], message: 'here' },
          { file: 1, range: [3, 0, 3, 2], message: 'and there' },
        ],
        notes: ['n1'],
      },
      { severity: 'error', code: 'E-Y', message: 'in std', file: 2, range: [0, 0, 0, 1], labels: [], notes: [] },
      { severity: 'error', code: 'E-Z', message: 'nowhere', labels: [], notes: [] },
    ],
  };
  const byFile = nav.diagnosticsByFile(fake);
  assert.deepStrictEqual([...byFile.keys()], ['a.sw']);
  const [d] = byFile.get('a.sw');
  assert.strictEqual(d.severity, 'warning');
  assert.strictEqual(d.message, 'm\nhere\nNote: n1');
  assert.deepStrictEqual(d.related, [
    { path: 'b.sw', std: null, range: [3, 0, 3, 2], message: 'and there' },
  ]);
});

test('workspace symbols: matching, ranking, and only the project', () => {
  const all = nav.workspaceSymbols(index, '');
  assert.ok(all.length > 20);
  assert.ok(all.every((s) => s.path === 'dot-notation.sw'));
  const length = nav.workspaceSymbols(index, 'length');
  assert.strictEqual(length[0].qualified, 'Main.Bag.length');
  assert.strictEqual(length[0].name, 'length');
  assert.strictEqual(length[0].container, null);
  assert.strictEqual(length[0].kind, 'def');
  assert.deepStrictEqual(length[0].range, [8, 8, 8, 14]);
  // a field is inside its type
  const field = nav.workspaceSymbols(index, 'age')[0];
  assert.strictEqual(field.qualified, 'Main.Person.age');
  assert.strictEqual(field.container, 'Main.Person');
  // letters in order, case-insensitively
  assert.ok(nav.workspaceSymbols(index, 'SHPDSC').some((s) => s.qualified === 'Main.Shape.describe'));
  assert.deepStrictEqual(nav.workspaceSymbols(index, 'zzzz'), []);
  // library symbols are not offered
  assert.ok(nav.workspaceSymbols(index, 'Std.').length === 0);
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

// Library documents (stitchwort-std:/List/Toolkit.sw): the lookups work in them
// from the index of a program that loaded the file. A synthetic index: file 0
// the program, 1 core.sw, 2 List/Toolkit.sw.
const libIndex = {
  version: 2,
  files: [
    { path: 'a.sw' },
    { path: 'crates/elab/src/std/core.sw', std: 'core.sw' },
    { path: 'crates/elab/src/std/List/Toolkit.sw', std: 'List/Toolkit.sw' },
  ],
  symbols: [
    { name: 'Std.Nat', kind: 'data', file: 1, range: [5, 5, 5, 8], container: null, type: 'Type' },
    { name: 'Std.List.sum', kind: 'def', file: 2, range: [3, 9, 3, 12], container: null },
  ],
  refs: [
    { file: 0, range: [0, 10, 0, 22], symbol: 1 },
    { file: 1, range: [20, 4, 20, 7], symbol: 0, type: 'Type' },
    { file: 2, range: [3, 9, 3, 12], symbol: 1 },
    { file: 2, range: [3, 30, 3, 33], symbol: 0, type: 'Type' },
  ],
};

test('library documents: path to std name, and entry by std', () => {
  assert.strictEqual(nav.stdOfPath('/List/Toolkit.sw'), 'List/Toolkit.sw');
  assert.strictEqual(nav.stdOfPath('/core.sw'), 'core.sw');
  assert.strictEqual(nav.fileIndexByStd(libIndex, 'core.sw'), 1);
  assert.strictEqual(nav.fileIndexByStd(libIndex, 'List/Toolkit.sw'), 2);
  assert.strictEqual(nav.fileIndexByStd(libIndex, 'Nope.sw'), -1);
});

test('inside a library file: a ref has a target in another library file, and uses are found across files', () => {
  const picked = nav.pickIndexForStd([{ key: 'k', index: libIndex }], 'List/Toolkit.sw', undefined);
  assert.strictEqual(picked.file, 2);
  const ref = nav.refAt(libIndex, picked.file, 3, 31);
  assert.strictEqual(ref.symbol, 0);
  const t = nav.targetOf(libIndex, ref);
  assert.deepStrictEqual({ std: t.std, range: t.range }, { std: 'core.sw', range: [5, 5, 5, 8] });
  assert.strictEqual(nav.hoverOf(libIndex, ref).name, 'Std.Nat');
  // Off a name there is no ref.
  assert.strictEqual(nav.refAt(libIndex, picked.file, 3, 20), null);
  // References from here: the declaration and the use in core.sw, and the use in this file.
  const refs = nav.referencesTo(libIndex, ref, true).map((r) => [r.std || r.path, r.range[0]]);
  assert.deepStrictEqual(refs, [['core.sw', 5], ['core.sw', 20], ['List/Toolkit.sw', 3]]);
  // The declaration's own name in a library file points at itself.
  const own = nav.refAt(libIndex, 2, 3, 10);
  assert.strictEqual(nav.targetOf(libIndex, own).std, 'List/Toolkit.sw');
});

test('which index serves a library document: the project it was opened from, if it has refs there', () => {
  const bare = { ...libIndex, refs: libIndex.refs.filter((r) => r.file === 0) };
  const a = { key: 'a', index: bare };
  const b = { key: 'b', index: libIndex };
  assert.strictEqual(nav.pickIndexForStd([a, b], 'core.sw', 'a').candidate.key, 'b'); // a has none in core.sw
  assert.strictEqual(nav.pickIndexForStd([b, { key: 'c', index: libIndex }], 'core.sw', 'c').candidate.key, 'c');
  assert.strictEqual(nav.pickIndexForStd([a], 'core.sw', 'a'), null);
  assert.strictEqual(nav.pickIndexForStd([b], 'Other.sw', undefined), null);
});
