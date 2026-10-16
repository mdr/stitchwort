# To do

The working list for Stitchwort. Reorder, edit or delete freely: the order of
**Next** is the order work happens in. Design detail lives in `DESIGN.md` and
`docs/proposals/`; this file only tracks what's to do and why.

How it's kept:
- Lanes that change performance run the benchmarks before merging
  (`nix develop -c cargo run --release -p stitchwort-bench`) and record an
  intended change with `-- --update`, saying why in the commit. The
  deterministic counts are checked by `nix flake check` (+10% fails).
- Significant design decisions (soundness, the kernel, language semantics)
  get a design note in `docs/proposals/` first, researched against the
  literature, and wait for the user (and possibly an external reviewer)
  before implementation.
- **Now** is what's in progress (ideally one thing).
- When something is finished, it moves to **Recently done** with its commit,
  and the oldest entries there are dropped (git log has the full history).
- New findings go under **Later** or **Known issues**, not straight into
  **Next**, unless they block what's in progress.

## Now

Work runs in lanes (up to three at once), each in its own git worktree and
branch, merged into `main` one at a time (with `nix flake check` after each). Only `main` edits
this file.

The main session orchestrates: it chooses lanes, hands each to a background
agent, then reviews, merges and updates this file.

Running:

Waiting on a decision: nothing.

## Next

In this order, after the in-flight lanes finish (the user: build a
capability we know we'll need before the work that needs it):

1. **Namespaces** (lane `namespaces-design`, docs only, in progress): the
   user decided qualified names (`List.sort`) and dot notation by type
   (`xs.sort`); `import List (map, filter)` for specific names only at first,
   meaning the same for namespaces now and files later; a small set of
   default-visible names (core types, constructors, operators); prefixed
   names removed. Design note written
   ([namespaces.md](docs/proposals/namespaces.md) draft 1, `Std` root,
   stage 0 binds built-in syntax to fixed library definitions first). The
   user answered §11 (implicit opening inside a namespace and extending
   library namespaces from user code are deferred; shadowing a type hides
   its default constructors). Reviewed: approved, with clarifications. Draft 2
   and stage 0 (built-ins bound to fixed declaration identities) merged as
   `06c78d2`. Stage 1 (namespaces, qualified names, `import`, the prelude
   in `Std`, every example rewritten) merged as `46d6578`. Stage 2 (dot
   notation by type, `e.f args`) merged (`dc201e6`); decisions in
   namespaces.md §9 "As built". Follow-ups: narrowing of speculative
   dependencies (mitigation 2); rewrite examples to dot notation; §5's
   mixed-kind example is accepted (records get no speculative edges) —
   user to confirm; `xs.map` needs list functions in `Std.List`. Noticed, not investigated: a signature
   `Comp NoOp NoRes Nat` behaves like `Nat`.
   Alongside, for Advent of Code: lane `aoc-survey` (Sonnet) surveys days
   1–5 of AoC 2025 from the user's solutions and inputs to rank what the
   library needs (merged: [aoc-2025.md](docs/aoc-2025.md)); the `Int` design
   note is written ([integers.md](docs/proposals/integers.md) draft 1: `Int` as
   a data type over `Nat`, no kernel change, Euclidean `/` and `%`); three
   questions answered (Euclidean `%`, `-x` on any expression, `%` on `Int`
   gives `Int`). Reviewed: approved (no kernel change; revise operator and
   literal typing first). Draft 2 merged (`3d8aa9d`): two-pass group rule
   for number types, prefix-minus rules, a 7-stage plan split Opus/Sonnet.
   Stage 1 (the type `OfNat | NegSucc`, its library, `Int.decEq`, three
   division conventions, `Text.toInt`, lemma checkpoint 1) merged
   (`d3753f8`); `OfNat`/`NegSucc` are visible unqualified for now (hiding a
   default type's constructors needs a namespaces mechanism). Next: stage 2,
   prefix minus and negative patterns in the parser (small, Sonnet); match
   the printer's minus precedence.
2. **Standard library for real programs** (ranked by the AoC survey,
   [aoc-2025.md](docs/aoc-2025.md): days 1–5 already run with today's
   compiler using hand-written helpers): a list toolkit, a `readAllLines`
   helper, `Nat` arithmetic lemmas (the gate to arithmetic proofs), `Nat`
   helpers (min, max, absDiff, pow, digits), sorting with a proof; later an
   `Array` type, a balanced map/set. Also: list functions (`map`, `filter`,
   folds, `sum`, `max`, `zip`, `take`/`drop`, indexing), sorting with a
   correctness proof (sorted permutation), `Int`, a balanced-tree map/set,
   grid helpers.
3. **Syntax conveniences**: design note draft 1 merged
   ([syntax-conveniences.md](docs/proposals/syntax-conveniences.md)):
   `where`/local functions and `match` lifted to hidden top-level
   definitions (no kernel change), pattern `let`/lambda, tuple sugar,
   result-type-first checking of calls. The user agreed with every
   recommendation in §8. Out for external review; implement after.
4. **Advent of Code 2025, early days** (decisions in aoc-2025.md: programs
   in `aoc/`, inputs and answers out of git, worked examples as tests), as a stress test with proofs where
   natural (sort correctness, parser round trips, worked examples by `rfl`).
   Inputs: the user's repo https://github.com/mdr/aoc-2025/tree/main/src/main/resources.
   Write up the friction found.

## Later

- **Benchmark gaps:** generated rows aren't benchmarked; `stitchwort run`
  isn't timed as a subprocess; no deterministic count catches loops that
  neither evaluate, recurse through a guarded pass nor allocate (e.g. the
  `expr.span()` walk in long chains).
- **Compact text stages 2–3** ([compact-text.md](docs/proposals/compact-text.md)
  draft 2): B1 (compact `List Char` in the evaluator) and selected B2
  natives. Prerequisites in draft 2: the expansion invariant, the list of
  passes to update, binding to declarations, an automatic build fingerprint
  in the test-cache key.
- **After merging number patterns:** regenerate JS snapshots and re-check
  the `TEXT_NATIVES` hashes in `crates/js/src/lib.rs` (`textTrim` and
  `natToText` depend on helpers that use number patterns).
- **Faster `textOfChars`** in JS (10⁶ characters: 98 ms) and stack-safe
  list helpers (`foldChars`, `compareChars`, …) when user code calls them
  directly.
- **(Done in stage 1 for JS) The JS limit on text:**
  in generated JS, prelude text operations stop at a few thousand
  characters (`length`, `append`, split, join, `==` aren't tail-recursive),
  with a catchable `StitchwortResourceError`. Measured in Node 22:
  `textLength` about 8,000, `textSplit`/`textJoin` about 5,500, `textToNat`
  about 3,000.
- **`Globals` fields `state` and `body` are `pub`**; make them private
  behind the admission API (with the mutual-recursion work).
- **More tail calls as loops in generated JS:** only a function's calls to
  itself (including in either branch of an `if`) are loops today. Not
  through `if h : P`, helpers like `maybeThen`, or between functions.
- **JS codecs are about 2× slower on small inputs** since they became
  iterative (5,000-element list: 0.3 → 0.7 ms both ways), if it matters.
- **JS encoding doesn't preserve sharing:** a result with much sharing is
  encoded once per path (`echoTree(dag(12))` gives 2^13−1 objects), so it
  can be exponential. Accept and document (done, DESIGN §12), or bound it.
- **JS strings are checked at every place they appear** (the same 1 MB
  string in 1,000 slots is scanned 1,000 times).
- **Hostile Proxies at the JS boundary:** `Array.isArray`, `length` and
  traps outside `own()` aren't wrapped, so a throwing trap escapes raw.
- **Nested recursive types** (`rest : Nest (Box a)`, probably rose trees
  `List Tree`) are refused with a misleading "negative position" message,
  and aren't supported.
- **Checking evaluates expensive input-independent expressions in `main`**
  (a `main` printing `spin 6000000` takes 2.4 s to check), which can tie
  up the playground's checker.
- **Browser tests** (`web/test.sh`) run only locally with Chrome; Firefox
  and Safari untested.
- **Mutual recursion stage 2 gaps:** a callback kept after its creator
  returns is tested only for single definitions; hash stability under
  reordering of identical-shaped members isn't tested (allowed to change);
  the playground doesn't show warnings (`W-MODULE-NAME`); for a body with
  no pattern match, termination errors point at the whole definition.
- **Mutual tail calls aren't loops in generated JS** (`isEven 10000000n`
  is a `StitchwortResourceError`).
- **Mutual data limits:** nested (`List Tree`), inductive-recursive and
  inductive-inductive types are out of scope; members' parameters must be
  written identically (names included); JS error paths alternating
  `.kids.first` aren't shortened.
- **`zonk` walks computations inside types recursively**, so a check like
  `textJoin … == t` on tens of thousands of characters runs out of
  resources while checking (found by compact text stage 2).
- **Compact text in the playground's WASM build** isn't measured.
- **`Term::Nat`'s hash doesn't include `Nat`'s own hash** (pre-existing).
- **JS internal-name encoding may collide** (from reading the code, not
  tested): a prime becomes `$` and a dot `$$`, and primes may appear
  mid-name, so `a''b` and `a.b` both become `$a$$b`. Namespaces stage 1
  added a new naming scheme with tests that names up to 4 characters are
  distinct; check whether this item is now closed.
- **Records follow-ups:** stage 2 (kernel projections and eta — deferred
  by the user until proofs about records need it; with the
  same-type rule and eta off in unification's `first_order` fallback;
  records.md draft 2 §7); `==` for records with proof or dependent fields;
  `(.name)` accessor sections; proof-field checks at the JS boundary for
  ordinary data types; printing `R.f r` as `r.f` in errors; descent through
  record fields for termination. After `->`, `{` starts an ability row, so
  a record literal in a result type needs parentheses.
- **`Partial` follow-ups:** a generated-program differential test of the
  runner against `crates/partial-model`; `mapP` in the library; the
  `E-PARTIAL-CALLBACK` note could point at polymorphic library variants. (Decided:
  an endless partial `main` in the CLI runs until stopped, like any
  program; no total-work limit.)
- **Measure the JS limits in browsers** (only Node so far).
- **Compact text** (text step 7): in generated JS first, then possibly in the
  checking evaluator, with differential tests against the plain-list version.
- **`==` operands are computed at check time.** `f x == y` puts `f x = y` in
  a type, so checking computes `f x`. Needs lazily evaluated values, or a
  translation of `==` that keeps its operands out of types.
- **Elaborating a chain is quadratic:** `expr.span()` and `may_perform` walk
  the whole subexpression at every level.
- **The WebAssembly guard size:** 128 KiB gives the playground about 25
  levels of nesting and list literals of about 200 elements. 256 KiB would
  roughly double that, with a 2× margin in Node. Separately, the parser's
  stack use per level could be cut (e.g. by boxing the `Diagnostic` in its
  `Result`).
- **Long list and text literals** stop at about 1,800 elements in a 2 MiB
  thread (about 75,000 in the CLI); waits on compact literals or checking
  literals without recursion.
- **The printer prints a function type's domain twice** in some branches,
  which may grow exponentially with nested domains (not measured).
- **Mutation testing** (in small sharded runs): the machine (`value.rs`),
  `budget.rs`, `native.rs` (167 mutants, never done).
- **Prove** `textToNat (natToText n) = Just n` (needs lemmas about `/` and
  `%`; tested only, for now).
- **`stitchwort run` out of resources** is tested only in the driver, not
  through the command (with the command's limits it needs about 1.5 GB).
  Perhaps a hidden option or environment variable to lower the limits.
- **Exit codes for `stitchwort run`:** every failure is 1. Decide whether
  "didn't check" and "failed while running" should differ.
- **`IO` operations that return `Result`** for recoverable errors (deferred
  by the text-and-IO proposal).
- **`decSucc` is no longer used in the prelude** (after the `decEqNat`
  fix); keep it for users or remove it.
- **For a kernel `decEqText` native** (compact text stage 3), follow the
  `decEqNat` pattern: make the definition ask a Boolean test so its `No` is
  `No (textNeq a b rfl)`, which the native can return, with whole-result
  tests.
- **`Partial`, someday/maybe** (see partial.md): stage 2, fuel-bounded runs
  inside total code and partial-correctness proofs ("if it finishes, it's
  right"), which needs a productive-observer argument and foreign calls kept
  out of steps; promoting partial code to total once termination is proven;
  equivalence of partial programs (research-level); handlers over `Delay`;
  JS exports of partial functions (a stepper).
- **Lacks constraints on row variables** aren't enforced (only reachable with
  a hand-written `Sig`).
- **Inferring a bare lambda's type** needs an annotation, e.g.
  `runState ((\n -> n) : Nat -> {Choose} Nat) …`.
- **Performance of effectful code** (deep handler trees) hasn't been measured.
- **Number patterns follow-ups:** rows after an equation that matches
  everything still add keys, so open terms can stay stuck needlessly (the
  `f6` example in number-patterns.md); prune unreachable rows before
  choosing keys. Default inequalities (`n ≠ k`) and `Char` literal patterns
  (`MkChar k _`) as later features.
- **Re-record benchmark times on a quiet machine** (the last `--update` ran
  under heavy load, so times were taken from earlier runs; counts are
  current).
- **Solving metavariables without recursion** (low priority: only large
  literal values in types hit it): `solve`, `rename`, `prune` and `zonk`
  still recurse over a solution. They're guarded, so a deep one is
  `E-RESOURCE`, but they share the stack: in the CLI,
  `theorem a : [1, …, n] = [1, …, n]` checks up to n = 56,875 with `rfl` but
  only 26,875 with `sym rfl`, whose hidden arguments are solved to the list.
- **DESIGN.md §16 open questions** that are still open (universes, handler
  admissibility and semantics, effects and dependency, `withFuel`, `Float`,
  the CLI name).

## Known issues


- **Row order is fixed by declaration order**, so `IO` (declared in the
  prelude) always comes first in a row: `{State Nat, IO}` and
  `{IO, State Nat}` are the same type. Harmless, but it means no test can
  put `IO` on the right of a row.
- **A misleading follow-on error** (found by the IO lane): after an
  `E-UNKNOWN-NAME` earlier in a file, a later `rfl` proof over a handled
  computation failed with "`rfl` proves an equation, but the expected type
  is `runPure (bind …)`". It checked once the first error was fixed.
- **In WebAssembly the stack guard measures the wrong stack.** Each call uses
  both the stack in linear memory (which the guard measures) and the
  engine's own call stack (about 1 MiB in V8), and the engine's runs out
  first. So the guard is set to 128 KiB there (`crates/web/build.rs`),
  calibrated in Node and Chrome only; Firefox and Safari are unmeasured.
  Eliminating recursion (steps 3 and 4) is the real fix.
- **The machine starts a nested machine** when a native forces an argument
  that's a solved metavariable (elaboration only). Bounded by the term, not by
  program depth, but it's the one exception to "no re-entry".
- **Memory per frame:** a million-deep recursion peaks at about 750 MB; the
  default limit is 2 million frames.
- **The differential test overflows in debug builds:**
  `the_evaluators_agree_on_the_prelude_and_every_example` overflows its
  64 MiB thread in a debug build (already so before step 4), at
  `examples/accept/io.sw`; release builds, which the gate uses, pass.
- **Agents' clean-up can hit the user's processes:** the depth-guards lane
  ran `pkill -f serve_forever`, which stopped the local playground server.
  Agent prompts now say to stop only processes they started, by PID.
- **`long n == long n` gives `E-RESOURCE` at 100,000 characters** in the
  reference evaluator (fine at 10,000); probably the "`==` operands are
  computed at check time" issue, unconfirmed.
- **Remaining surviving mutants** judged equivalent or unreachable:
  `effects.rs` lines 223 (×3), 403, 414, 706 (×2), 709, 745, 844;
  `termination.rs` line 111 (`>` → `>=`); the `auto` fix in step 1 (masked
  by the sticky budget).

## Recently done

- `df63a82` Fixed a compiler panic after a failed record type (failed data groups now resolve as failed), and `else`/`then` on their own lines continue an `if`.
- `d567dfc` Playground: warnings shown apart from errors, a phone layout (viewport, no sideways scroll), the JavaScript tab shown in full; 21 browser tests.
- `6a790a1` `Partial` stage 1: `{Partial}` in types; partial groups translated into ordinary checked declarations over an opaque `Delay`; the runtime steps them (one tick per recursive call, matching `crates/partial-model` trace for trace); `main` can loop until end of input; total code can't run partial code; JS erases `Delay`.
- `22d7b01` Records stage 1: declared records (`type Person = { name : Text, age : Nat }`), `p.name`, `{ p | age = … }`, record patterns, dependent and proof fields, evaluation order as written, derived `==` where provable; JS plain objects with proof fields validated at the boundary; every data type's hash now includes its field names.
- `1965faf` Compact text stage 2: text literals are one compact term in the kernel (shared character ranges), indistinguishable from the list they stand for; long literals from ~1,800 (2 MiB thread) to over 4 million characters; a build fingerprint and modes in the test-cache key; ~28,000 whole-result comparisons and mutation evidence.
- `1c2addc` Mutual recursion stage 3: mutual data types (`Tree`/`Forest`, `Even`/`Odd`, three-member groups) checked as a unit; positivity across the group (`Bad1`/`Bad2` refused; the mutant proved `Void`); no data from `Prop` groups; group hashing; million-deep `Tree`/`Forest` across the JS boundary. Mutual recursion is complete.
- `358fec5` `Partial` draft 3 (stage 1 only; later stages someday/maybe) and `crates/partial-model`, an executable model of the stage-1 runtime running the reviewer's test table.
- `af02abc` Mutual recursion stage 2: declarations in any order within a file, function groups checked as a unit by the kernel (`define_group`), witness messages naming each member, group hashing, `auto` diagnostics explaining unavailable candidates, one JS calling convention; mutation evidence including the Rocq-bug shape.
- `73899f9` Playground polish: 18 headless-Chrome tests (`nix develop -c ./web/test.sh`), streamed run output (Stop keeps what was printed), Tab/undo and resize fixed, `E-INPUT` after 10,000 reads past end of input.
- `01208f2` Natives match their definitions as whole results, proofs included: `decEqNat` redefined so its `No` proof is small and the native returns exactly it (new native `eqNatSound`); every native audited; natives-on/off whole-result tests including numbers above 2^64.
- `9eb1487` Size-change termination for single definitions: Ackermann, swapped arguments and `merge` accepted; partial recursive calls refused with a suggested lambda; one shared entry arity; compared with the old checker on 20,000 generated programs (the new one accepts all the old one did except 7 partial calls).
- `4776303` JS boundary follow-ups: decoders read only own properties (blocks prototype pollution), shared input decoded once (a 60-level DAG went from never finishing to instant), the generator refuses a definition without a body, DESIGN's boundary table matches what's built.
- `813fe74` Number patterns: a number switch in kernel case trees; the 256 cap is gone (`statusText 404` works, 10^30 too); `f 256` checks in 0.01 s instead of 2 s; 3 columns × 5 keys from 85 s to under a millisecond; constructor-expansion oracle over 300 generated definitions.
- `72d3004` Mutual recursion phase 1: draft 3 of the design and the size-change graph algorithm (`sct.rs`), with an independent reference implementation and mutation evidence.
- `afad1e0` Kernel admission ([kernel-admission.md](docs/proposals/kernel-admission.md)): declarations are pending, final or failed, and may refer only to final ones; closes a split cycle (`f 0` looping) and `impossible MakeD : Void` via the raw kernel API; 11 must-reject tests.
- `f31d1c9` Compact text stage 1: `Text` is a JS string in generated code with 14 native operations bound to the prelude definitions by hash; prelude text operations handle over 4 million characters in Node (from ~5,000–8,000).
- `84bc590` JS boundary hardening: names can't collide by construction (field `tag` becomes `$tag`, exports aliased, reserved names refused), iterative codecs (a million-element list in about 0.2 s), clearer boundary errors.
- `07550ff` Recorded benchmarks (`crates/bench`, `bench/baseline.toml`): deterministic counts (steps, visits, allocations, peak heap) checked in `nix flake check`; timings reported, not checked.
- `017d554` Text step 3 (js-text lane, merged): `Text` and `Char` as JS strings with strict decoding, parameterised data types at the boundary, self tail calls as loops, `StitchwortResourceError`.
- `ccebba3` Syntax colouring in the playground's editor (CSS Custom Highlight API, with a fallback); restoring the saved draft on reload fixed.
- `d166039` Stack-safe step 4 (depth-guards lane, merged): every recursive pass guarded by stack use; deep nesting is `E-RESOURCE` natively and in WebAssembly (`crates/driver/tests/nesting.rs`).
- `f35f1a7` Text step 6 (playground-run lane, merged): the playground's Run button and its compiler in Web Workers, replaced after a crash. View it locally with `web/serve.sh`.
- `65f91ce` Text step 5 (run lane, merged): `main` and `stitchwort run`, tested against `simulate` and real standard input and output; `examples/accept/adder.sw`.
- `3fb4764` Text step 4 (IO lane, merged): the `IO` ability and `simulate`, `examples/accept/io.sw`, `examples/extract/io.sw`.
- `fae5cc2` Stack-safe step 3: `conv`, `unify` and `quote` as work lists; iterative freeing of terms.
- `78a9ddc` Local WebAssembly test page: `web/stress.html`, served by `web/serve.sh`.
- `5caa024` `unsafe` allowed with a written justification (lint `deny`, was `forbid`).
- `cdfae0d` Stack-safe step 2: the abstract machine, the reference evaluator, differential tests, iterative freeing of values.
- `14ac90d` Every sub-term the evaluator runs is behind its own `Rc`.
- `2942e55` Checking computes an argument only when a type needs it.
- `e53c53f` Stack-safe step 1: resource errors and per-operation budgets.
- `02235d8` Constructor fields shared (fixed quadratic list recursion).
- `0878284` Text step 2: `Text`, its operations and laws, `++`.
- `01313d1` Text step 1: `Char`, literals and escapes.
