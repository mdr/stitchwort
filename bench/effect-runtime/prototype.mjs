// A hand-written prototype of the runtime recommended in
// docs/proposals/effect-runtime.md, made by patching the JS that
// `stitchwort build --js` generates for bench/effect-runtime/map.sw. Usage:
//
//   stitchwort build --js bench/effect-runtime/map.sw -o OUT
//   node bench/effect-runtime/prototype.mjs OUT/map.js OUT/map-loop.js [--parameter]
//   node bench/effect-runtime/export.mjs OUT/map-loop.js
//
// It replaces the four library functions that take a computation apart
// (`Effect.bind`, `Effect.foldComp`, `Effect.translate`, `Effect.runPure`):
//
// - `bind c k` builds a `Bind` node and calls nothing, so a long chain of
//   effectful calls never deepens the JS stack;
// - the eliminators run a computation with a loop that keeps the pending
//   continuations on a linked list in the heap (one cell per `bind`), so
//   reaching the next operation is linear in the work done, and capturing the
//   continuation at an operation is taking a pointer to that list (no copy:
//   the list is never changed, so a continuation can be resumed any number of
//   times).
//
// With `--parameter`, `Counter.number` (a handler that passes its state as a
// function argument) is also replaced by the loop a backend would generate
// for a handler with a parameter: the state is a variable of the loop, and a
// clause that ends with `k v s'` continues the loop instead of calling `k`.
// That is the part a backend has to recognise; the rest is generic.
//
// Everything else in the module is left as generated. The prototype is only
// evidence for the note: it is not how the backends would be changed.
import { readFileSync, writeFileSync } from "node:fs";

const [input, output, ...flags] = process.argv.slice(2);
let source = readFileSync(input, "utf8");
// With `--lazy-resume` (added by effect-runtime-review.md), a handler's `k`
// doesn't run the rest of the computation when called: it returns a `Bind`
// node that does, for whoever runs the handler's result. Sound because every
// `foldComp` the elaborator makes (`handle`) folds into a computation of the
// row outside; at the empty row the clause's `k` is wrapped in `runPure`,
// which runs the node at once, so only handlers with abilities left over
// gain.
const lazy = flags.includes("--lazy-resume");

const replaceDefinition = (name, replacement) => {
  const start = source.indexOf(`const ${name} = `);
  if (start < 0) throw new Error(`no definition of ${name}`);
  const lineEnd = source.indexOf("\n", start);
  const firstLine = source.slice(start, lineEnd);
  // A multi-line definition ends at the first line that is `};`.
  const end = firstLine.trimEnd().endsWith("{") ? source.indexOf("\n};\n", start) + 4 : lineEnd + 1;
  source = source.slice(0, start) + replacement + "\n" + source.slice(end);
};

const runtime = `
// --- prototype runtime (bench/effect-runtime/prototype.mjs) ---
// A stack of pending continuations: null, or { k, next }.
// Runs \`c\` with \`stack\` pending until it finishes with nothing pending
// (returns the \`Done\` node) or reaches an operation (returns
// { o, rest, stack }: resuming with y runs rest(y) with that stack pending).
function $proto$run(c, stack) {
  for (;;) {
    switch (c.tag) {
      case "Bind":
        stack = { k: c.k, next: stack };
        c = c.c;
        break;
      case "Done":
        if (stack === null) return c;
        c = stack.k(c.value);
        stack = stack.next;
        break;
      case "Call":
        return { tag: "Op", o: c.o, rest: c.rest, stack };
      default:
        throw new Error("not a computation: " + c.tag);
    }
  }
}
function $proto$fold(done, call, c, stack) {
  const r = $proto$run(c, stack);
  if (r.tag === "Done") return done(r.value);
  const rest = r.rest, pending = r.stack;
  return call(r.o)(${lazy
    ? `(y) => ({ tag: "Bind", c: { tag: "Done", value: y }, k: (z) => $proto$fold(done, call, rest(z), pending) })`
    : `(y) => $proto$fold(done, call, rest(y), pending)`});
}
function $proto$translate(m, c, stack) {
  const r = $proto$run(c, stack);
  if (r.tag === "Done") return r;
  const o = r.o, rest = r.rest, pending = r.stack;
  return { tag: "Call", o: $Std$dEffect$dsigInject(m)(o),
    rest: (x) => $proto$translate(m, rest($Std$dEffect$dsigReply(m)(o)(x)), pending) };
}
// --- end of prototype runtime ---
`;

replaceDefinition("$Std$dEffect$dbind", "const $Std$dEffect$dbind = (c) => (k) => ({ tag: \"Bind\", c, k });");
replaceDefinition("$Std$dEffect$dfoldComp", "const $Std$dEffect$dfoldComp = (done) => (call) => (c) => $proto$fold(done, call, c, null);");
replaceDefinition("$Std$dEffect$dtranslate", "const $Std$dEffect$dtranslate = (m) => (c) => $proto$translate(m, c, null);");
replaceDefinition("$Std$dEffect$drunPure", "const $Std$dEffect$drunPure = (c) => $proto$run(c, null).value;");

if (flags.includes("--parameter")) {
  // What a backend would emit for
  //   handle prog() with
  //     | return x => (s => x)
  //     | Counter.next u, k => (s => k s (s + 1))
  // The row outside is empty, so every operation is `next` (in the left of
  // the row's `Plus`).
  replaceDefinition(
    "$Main$dCounter$dnumber",
    `const $Main$dCounter$dnumber = (prog) => (s0) => {
  let s = s0;
  let r = $proto$run(prog({ tag: "UnitValue" }), null);
  for (;;) {
    if (r.tag === "Done") return r.value;
    // \`next\`: k s (s + 1), a tail call of k, so the loop goes on.
    const answer = s;
    s = $Std$dNat$dadd(s)(1n);
    r = $proto$run(r.rest(answer), r.stack);
  }
};`,
  );
}

// The runtime goes before the first generated definition.
const at = source.indexOf("const $Std$d");
source = source.slice(0, at) + runtime + "\n" + source.slice(at);
writeFileSync(output, source);
console.log(`wrote ${output}`);
