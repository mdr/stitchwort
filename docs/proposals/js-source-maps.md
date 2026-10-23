# Source maps for generated JavaScript

Status: exploration, with a working prototype of the per-definition option.
Decisions at the end (D940 onward).

## 1. The problem and what users would get

A TypeScript app that calls an exported Stitchwort module sees a stack trace
or debugger breakpoint in the generated JS (`$Main$dleaves`, `trees.js:677`),
not the `.sw` source. A source map (standard v3) fixes both: the tool shows
`trees.sw:10:12` and the name `leaves`.

What the prototype produces, from `stitchwort build --js trees.sw
--source-map -o out`, running a deliberately too-deep input under
`node --enable-source-maps` (the `cause` of the resource error is the
engine's `RangeError`):

```
StitchwortResourceError: leaves: ran out of resources (...)
    at outOfResources (out/trees.js:25:7)
    at Module.$$leaves (.../trees.sw:10:12)
    at t.mjs:4:7
  [cause]: RangeError: Maximum call stack size exceeded
      at leaves (.../trees.sw:10:12)
      at leaves (.../trees.sw:10:12)
      ...
```

Before the map, the same frames read `at $Main$dleaves (out/trees.js:677:29)`.
Line 10 of `examples/extract/trees.sw` is `export def leaves: Tree -> Nat`.
The first frame is the runtime glue (`outOfResources`), which has no source and
stays unmapped, correctly.

Consumers:

- Node: `--enable-source-maps` (or `NODE_OPTIONS`), applied to `error.stack`,
  uncaught errors, and `cause` chains (shown above). `module.findSourceMap`
  gives the lookup API (used in the prototype's investigation).
- Chrome and Firefox devtools: read `//# sourceMappingURL` and show the `.sw`
  file, with breakpoints settable in it. They need the source text, either
  fetchable at the relative path or in `sourcesContent`.
- Vite dev server and Vitest (which runs through Vite's transform pipeline):
  when no plugin loads a module, Vite reads it from disk and calls
  `extractSourcemapFromFile`, which picks up an inline or adjacent map and
  uses it as the module's input map (`transformRequest.ts`, `loadAndTransform`;
  a failure is only a warning). So a `.js` plus `.js.map` in the app works as
  is. For production builds I believe Vite's load fallback does the same, and
  esbuild reads linked or inline input maps when bundling; plain Rollup does
  not without a plugin. These two I have not verified; the Vite dev path is
  from its source.

Choices:

- Separate `X.js.map` versus inline (`data:` URL comment). Separate keeps the
  `.js` readable and small and is what the prototype does. Inline survives
  copying the one file but bloats it. Offer separate first; inline is a flag
  later if asked.
- `sourcesContent`. Paths alone need the `.sw` files to be readable from where
  the debugger looks. The embedded library (`<prelude>`, `std/...`) has no file
  on disk at all, so the prototype puts the text of those in the map
  (`stitchwort:<prelude>`) and uses relative paths for files on disk. Cost:
  the prelude text dominates the map. For `trees.sw` the map is 97 KB beside a
  30 KB module, almost all of it the prelude's source. Better: drop mapping
  for library definitions (Section 3) or ship the library text once.
- Committing generated files. Maps are deterministic (the same source gives
  the same map; the test asserts it), and sources are paths relative to the
  output directory, so they are stable across machines as long as the layout
  is. Absolute paths would break that and are never written.

## 2. Where positions come from

Spans (`Span { file, start, end }`, `crates/syntax/src/source.rs:16`) are
byte ranges and flow like this today:

- Parser to elaborator: every expression has a span; `infer` wraps each
  elaborated term in `Term::Loc(span, term)` (`crates/elab/src/check.rs:558`),
  and `check` mode does too (`check.rs:1542`, `2160`), as do numbers and
  literals (`numbers.rs:1047`, `lib.rs:3318` and others, about 35 sites).
- Kernel: `check` and `infer` keep `Loc` nodes in the terms they return
  (`crates/core/src/check.rs:222`, `411`), so an admitted body still has them.
  The check cache serialises them (`crates/elab/src/cache/codec.rs:409`), so
  cached library bodies keep spans too (not tested).
- Each definition has `Def.span` (`crates/core/src/globals.rs:~83`). The JS
  generator already uses it for diagnostics (`lib.rs`, "while generating
  JavaScript for this").
- The JS generator builds strings straight from core `Term`s; there is no IR
  with positions. It discards `Loc` as it goes (`Gen::expr`,
  `crates/js/src/lib.rs`: `Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env)`).
  The runtime interpreter's lowering (`crates/rt/src/lower.rs:455`) discards
  it as well, so `rt` carries no spans; that matters only for a `run` mapping,
  not for JS.

What is lost or absent:

- Erasure (`crates/rt/src/erasure.rs:121` strips `Loc`/`Ann` when it peels):
  no loss of anything that runs; only erased proofs vanish.
- Inlining (`Gen::tail`, helpers inlined into a tail-recursive loop) and the
  tail-recursion-modulo-constructor loops: the generated code mixes the
  helper's and the definition's text. Per-definition mapping is unaffected
  (it is all inside the one `const`). Per-expression would attribute inlined
  text to the helper's own `Loc`, which is right.
- Natives (`const $Std$dNat$dadd = (a) => (b) => a + b;`): map to the
  library definition, which is a library source line, not user code.
- Generated definitions: derived instances, record accessors, and the like
  have a `Def.span`, but I did not verify what they point at (likely the
  declaration that caused them). Check in stage 1.
- The runtime, the codecs and the export wrappers' decode and encode code are
  glue. The prototype maps a wrapper to its export's `def`, which is useful: an
  `StitchwortInputError` thrown there then reads as "in `leaves`".

Granularity achievable: per definition today, with no changes to elaboration.
Per expression is possible because the data exists, but the emitter returns
`String`s from `expr`, `tree` and about 30 helpers, so spans would have to be
threaded through every return value (Section 3).

## 3. Options

(a) Per definition (built). The generator records, for each emitted
definition and wrapper, its first line and a span; the encoder
(`crates/js/src/sourcemap.rs`, about 300 lines with a tiny VLQ encoder and a
decoder for tests) turns that into JSON. Each generated line of the definition
gets a segment at column 0, and the identifier gets a labelled segment so
`names` has `leaves`. The position is the name after `def` (found by looking
in the span's text; falls back to the span start), so a frame lands on the
`def` line. A terminator (a one-field segment) ends each run so glue after it
is not attributed to the last definition.
- Cost: done in under a day. `Output` gains `mappings`; the JS text is
  unchanged, so no snapshot moves. Nothing is emitted unless `--source-map` is
  given, and the only change then is a trailing `//# sourceMappingURL` line.
- Risk: low. It is read-only on generation. Determinism holds (per-run state
  is only the order of definitions, already stable).
- Weak point: every frame in a long definition reports the `def` line, not the
  failing expression. For short Stitchwort definitions this is often enough.

(b) Per expression or statement. Make `expr`/`tree` return text plus mapping
points (or emit sentinel comments and strip them afterwards, which is hacky
but small). `Term::Loc` nodes are already where needed. Complications:
- inlining and loops duplicate or reorder text, so each fragment's offset must
  be tracked as it is wrapped (`format!` calls everywhere);
- a `Loc` on almost every sub-expression gives dense maps (output size grows
  with expression count; the segments are small, but a map several times the
  module's size is plausible);
- spans are `Loc` of elaborated terms, including those the elaborator
  synthesised; some map to odd places.
- Cost: several days to a week, high churn in the biggest file (4200 lines),
  moving risk into the generator everyone else edits. Value is highest for
  debugging case trees and branches inside big definitions.

(c) Alternatives.
- Statement-level only for `case` branches: record a segment at each branch
  of `Gen::tree` (about 5 sites, the `Branch` has a body `Loc`). Gives
  "which pattern arm" for most real bugs at a fraction of (b)'s cost. A good
  stage 2.
- Library definitions unmapped (or `ignoreList`, the v3 `x_google_ignoreList`
  field, so devtools hide them from stacks). This fixes the map size and
  removes the prelude's `sourcesContent`. Easy; worth doing with (a).
- Leave it to users: write the map downstream from `.d.ts`/`.js`; no.

## 4. Prototype

Flag: `stitchwort build --js TARGET --source-map [-o DIR]` (files and project
namespaces). Writes `NAME.js.map` beside `NAME.js` and appends the comment.

Files: `crates/js/src/sourcemap.rs` (new), `crates/js/src/lib.rs` (the mapper
calls around each definition and wrapper, and `Output.mappings`),
`crates/cli/src/main.rs` (flag, relative paths, writing).

Behaviour notes:
- Paths: a source on disk is written relative to the output directory (project
  files are found through the project folder); the embedded library becomes
  `stitchwort:<name>` with its text in `sourcesContent`; the others `null`.
- Columns are UTF-16 code units, as the format asks.
- Bug found while building it: `js_string_literal` emits `\u{a}`, which is JS
  and not JSON, and Node silently ignored the whole map. The map has its own
  JSON string writer now. A reminder that consumers fail quietly.
- The existing extract snapshots do not change: the JS text is the same
  with the flag off, and `stitchwort-js` output only adds a field.

Test: `source_maps_point_generated_definitions_at_their_source` in
`crates/cli/tests/extract.rs` checks that the JS has no map comment by
default; the map is deterministic; the generated `leaves` and its wrapper
decode (with the test's own VLQ decoder) to `trees.sw`, the line of
`export def leaves`; the runtime lines before the first definition map nowhere;
and Node, run with `--enable-source-maps`, prints a stack with
`trees.sw:10:12` for the `cause`. Unit tests for the VLQ coding are in
`sourcemap.rs`.

## 5. Recommendation and staging

Ship (a) with library definitions left out of the map (stage 1), because it
solves "stack trace shows the right `.sw` def" cheaply and safely and the
prototype shows it works in Node today. Then the branch-level mapping from (c)
if people find def-level too coarse. Do (b) only if a real debugging need
shows up. Keep it off by default so committed generated files stay as they
are; consider turning it on when an `--out` project config exists.

Stages:
1. Land the prototype; map user files only (library definitions unmapped, so
   no `sourcesContent` for them); verify derived and generated definitions;
   verify Vite production build and esbuild consumption with a real app.
2. `case` branch segments.
3. Maybe inline maps, `run --js` mapping (the run program is a different
   generator in `run.rs`), and the playground.

## Decisions

D940. Land the per-definition source map as an opt-in flag on `build --js`?
[Yes. It's small, off by default, and no existing output changes.]

D941. Should library definitions (prelude, `std/`) appear in the map?
[No. Leave them unmapped so the map stays small and stacks show your code
first; revisit if people want to step into the library.]

D942. Separate `.js.map` files or inline in the `.js`?
[Separate files, with inline as a later flag if asked. Keeps generated files
readable and diffs small.]

D943. Write `sourcesContent` for user files?
[No. Use relative paths, since the `.sw` files travel with the project;
add a flag if someone ships the JS without the source.]

D944. Should we go on to branch-level (case arm) mapping?
[Wait until a user finds def-level too coarse; it is a small follow-up
(about five sites), unlike full per-expression mapping.]

D945. Per-expression mapping through the emitter?
[No, not now. It touches the largest file everywhere and the payoff is
modest next to branch-level mapping.]
