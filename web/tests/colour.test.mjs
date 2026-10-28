// The playground tokenizer's glued-numeral colouring (colour() in
// web/index.html), run in node: the function is cut out of the page's module
// script and evaluated. Run with `node --test web/tests/colour.test.mjs`.
import test from "node:test";
import assert from "node:assert";
import { readFileSync } from "node:fs";

const html = readFileSync(new URL("../index.html", import.meta.url), "utf8");
const from = html.indexOf("const KEYWORDS = new Set(");
const to = html.indexOf("const highlighted = document.getElementById");
assert.ok(from > 0 && to > from, "colour() not found in web/index.html");
const colour = new Function(`${html.slice(from, to)}; return colour;`)();

/** The [kind, text] stretches of `text`. */
function marks(text) {
  const out = [];
  colour(text, (kind, start, end) => out.push([kind, text.slice(start, end)]));
  return out;
}
const numbers = (text) => marks(text).filter(([k]) => k === "number").map(([, t]) => t);

test("glued numerals", () => {
  assert.deepStrictEqual(numbers("f -1"), ["-1"]);
  assert.deepStrictEqual(numbers("x-1"), ["1"]);
  assert.deepStrictEqual(numbers("x - -1"), ["-1"]);
  assert.deepStrictEqual(numbers("x*-1"), ["-1"]);
  assert.deepStrictEqual(numbers("d :=-1"), ["-1"]);
  assert.deepStrictEqual(numbers("-1.5"), ["-1.5"]);
  assert.deepStrictEqual(numbers("if c then-1 else 2"), ["-1", "2"]);
});
