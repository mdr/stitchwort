// Benchmark of the generated JS boundary codec (bench/js-codec/README in
// doc.sw's header). Usage:
//
//   stitchwort build --js bench/js-codec/doc.sw -o OUT
//   node bench/js-codec/bench.mjs OUT/doc.js [--cpu-prof-friendly] [--runs N]
//
// A document of about an hour of speech (9,000 words, 1,000 segments, 20
// notes, a few tags) goes in twice and out once, as in `merge`. The phases are
// timed on their own, each warm, as the median of many runs:
//
//   decode  the generated module's own `decode` of a document,
//   body    the Stitchwort `merge` on two decoded documents,
//   encode  the module's own `encode` of the result,
//
// and so are the whole exported calls `roundTrip(doc)` and `merge(a, b)`.
//
// The module's internals aren't exported, so the generated source is copied
// to a temporary file with a few exports added at the end, which call the
// module's own `decode`, `encode` and `merge`.
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const args = process.argv.slice(2);
const file = resolve(args.find((a) => !a.startsWith("--")) ?? "doc.js");
const runsAt = args.indexOf("--runs");
const RUNS = runsAt >= 0 ? Number(args[runsAt + 1]) : 300;
const WARM = 100;

const source = readFileSync(file, "utf8");
const dir = mkdtempSync(join(tmpdir(), "sw-bench-"));
// What the epilogue calls depends on how the module is generated; the
// internal names it uses are the module's own.
const fast = /decodeFast\((dec\$\d+), (ty\$\d+)[^]*?encodeFast\((enc\$\d+), (ty\$\d+)/.exec(source);
const epilogue = fast
  ? `export const __bench = {
  decode: (x) => decodeFast(${fast[1]}, ${fast[2]}, x, "d"),
  encode: (v) => encodeFast(${fast[3]}, ${fast[4]}, v),
  merge: $Main$dmerge,
};`
  : `export const __bench = {
  decode: (x) => decode(data(info$Main$dDoc), x, "d"),
  encode: (v) => encode(data(info$Main$dDoc), v),
  merge: $Main$dmerge,
};`;
const path = join(dir, "doc.mjs");
writeFileSync(path, `${source}\n${epilogue}\n`);
const m = await import(pathToFileURL(path).href);
const { decode, encode, merge: body } = m.__bench;

// A deterministic generator.
let seed = 12345;
const rnd = (n) => {
  seed = (Math.imul(seed, 1103515245) + 12345) & 0x7fffffff;
  return seed % n;
};
const vocabulary = Array.from({ length: 2000 }, (_, i) => {
  const len = 2 + (i % 9);
  let s = "";
  for (let k = 0; k < len; k++) s += String.fromCharCode(97 + ((i * 7 + k * 13) % 26));
  return i % 50 === 0 ? `${s}é` : s;
});

const makeDoc = (id) => {
  const words = [];
  let t = 0;
  for (let i = 0; i < 9000; i++) {
    const length = 100 + rnd(600);
    words.push({ text: vocabulary[rnd(vocabulary.length)], start: t, length });
    t += length + rnd(200);
  }
  const segments = [];
  for (let i = 0; i < 1000; i++) {
    segments.push({ id: `seg-${id}-${i}`, start: i * 3600, length: 3000 + rnd(500) });
  }
  const kinds = ["plain", "todo", "quote"];
  const notes = [];
  for (let i = 0; i < 20; i++) {
    const note = { id: `note-${id}-${i}`, kind: kinds[i % 3], body: `A note, number ${i}, about something.` };
    if (i % 2 === 0) note.at = rnd(1000000) - 500000;
    notes.push(note);
  }
  const tags = {};
  for (let i = 0; i < 8; i++) tags[`tag${i}`] = `value ${i}`;
  return {
    title: `Meeting ${id}`,
    meta: { speaker: "Ada", language: "en-GB", revision: id, ...(id % 2 ? { summary: "A long talk." } : {}) },
    status: id % 2 ? { type: "final", reviewer: "Grace", revision: 3 } : { type: "draft" },
    words,
    segments,
    notes,
    tags,
    ...(id % 2 ? { parent: "root" } : {}),
  };
};
const a = makeDoc(1);
const b = makeDoc(2);

const median = (xs) => xs.slice().sort((x, y) => x - y)[xs.length >> 1];
const time = (f) => {
  for (let i = 0; i < WARM; i++) f();
  const samples = [];
  for (let i = 0; i < RUNS; i++) {
    const t0 = process.hrtime.bigint();
    f();
    samples.push(Number(process.hrtime.bigint() - t0) / 1e6);
  }
  return median(samples);
};

// Correctness first: a round trip gives back an equal document.
assert.deepStrictEqual(m.roundTrip(a), a);
const merged = m.merge(a, b);
assert.equal(merged.title, a.title);
assert.equal(merged.notes.length, 40);

const decodedA = decode(a);
const decodedB = decode(b);
const result = body(decodedA)(decodedB);
const rows = [
  ["decode (one doc)", time(() => decode(a))],
  ["body (merge)", time(() => body(decodedA)(decodedB))],
  ["encode (one doc)", time(() => encode(result))],
  ["roundTrip(doc)", time(() => m.roundTrip(a))],
  ["merge(a, b)", time(() => m.merge(a, b))],
];
for (const [name, ms] of rows) console.log(`${name.padEnd(18)} ${ms.toFixed(3).padStart(9)} ms`);
