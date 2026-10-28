'use strict';
// The glued-numeral rule of the TextMate grammar (docs/proposals/negative-arguments.md):
// a `-` glued to a numeral, with no closing character touching it on the left,
// is part of the number. Only the grammar's regular expressions are exercised,
// with JavaScript's engine (lookbehind works the same as in Oniguruma here).
const test = require('node:test');
const assert = require('node:assert');
const path = require('node:path');
const grammar = require(path.join(__dirname, '..', 'syntaxes', 'stitchwort.tmLanguage.json'));

function numberPatterns(node, out = []) {
  if (node && typeof node === 'object') {
    if (node.name === 'constant.numeric.stitchwort' && node.match) out.push(new RegExp(node.match, 'g'));
    for (const v of Object.values(node)) numberPatterns(v, out);
  }
  return out;
}

/** The texts coloured as numbers; earlier patterns take their span first. */
function numbers(text) {
  const taken = new Array(text.length).fill(false);
  const found = [];
  for (const re of numberPatterns(grammar)) {
    for (const m of text.matchAll(re)) {
      const end = m.index + m[0].length;
      if (taken.slice(m.index, end).some(Boolean)) continue;
      taken.fill(true, m.index, end);
      found.push([m.index, m[0]]);
    }
  }
  return found.sort((a, b) => a[0] - b[0]).map((f) => f[1]);
}

test('glued numeral colouring', () => {
  const cases = [
    ['f -1', ['-1']],
    ['x-1', ['1']],
    ['x - -1', ['-1']],
    ['x*-1', ['-1']],
    ['d :=-1', ['-1']],
    ['-1.5', ['-1.5']],
    ['f(-1)', ['-1']],
    ['xs[0]-1', ['0', '1']],
  ];
  for (const [text, expected] of cases) {
    assert.deepStrictEqual(numbers(text), expected, text);
  }
});

test('after a keyword the grammar cannot see the word, so it does not glue', () => {
  // The playground treats `then-1` as a negative numeral (a keyword is not a
  // closing token); a TextMate lookbehind sees only one character, so here
  // `then-1` colours the `1` and leaves the `-` as an operator.
  assert.deepStrictEqual(numbers('then-1'), ['1']);
});
