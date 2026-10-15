# To do

The working list for Stitchwort. Reorder, edit or delete freely: the order of
**Next** is the order work happens in. Design detail lives in `DESIGN.md` and
`docs/proposals/`; this file only tracks what's to do and why.

How it's kept:
- **Now** is what's in progress (ideally one thing).
- When something is finished, it moves to **Recently done** with its commit,
  and the oldest entries there are dropped (git log has the full history).
- New findings go under **Later** or **Known issues**, not straight into
  **Next**, unless they block what's in progress.

## Now

- **Stack-safe evaluation, step 3**
  ([proposal](docs/proposals/stack-safe-evaluation.md)): conversion (`conv`)
  as a work list, iterative `quote`, and iterative freeing of `Term`. Tests:
  two independently built long lists compared (equal, differing at the head,
  differing only at the end); printing a 10⁵-element value; freeing deep
  terms.

## Next

1. **Stack-safe evaluation, step 4:** depth guards in the parser, elaborator,
   unifier, kernel, hasher, termination checker, JS generator and printer,
   tested in subprocesses just past each limit. Measure what deep programs do
   in the WebAssembly playground (linear-memory stack and the engine's own
   call-stack limit).
2. **Text, step 3** ([proposal](docs/proposals/text-and-io.md)): JS encoders
   and decoders for `Text` and `Char`, the boundary tests (surrogates, NUL,
   noncharacters, both round-trip laws), and differential tests including the
   cross-runtime counterexamples. Decide how generated JS copes with long
   texts, since JS engines don't eliminate tail calls.
3. **Text, step 4:** the `IO` ability and `simulate`.
4. **Text, step 5:** `main` and `stitchwort run`, tested against `simulate`
   and real standard input and output.
5. **Text, step 6:** the playground's Run button. Also show tests that ran out
   of resources as such (today they show as not passed), give the playground
   its own smaller limits, and republish it
   (https://claude.ai/artifact/T7p2cjuvWBGWdiEdCQVLcj).

## Later

- **Compact text** (text step 7): in generated JS first, then possibly in the
  checking evaluator, with differential tests against the plain-list version.
- **`==` operands are computed at check time.** `f x == y` puts `f x = y` in
  a type, so checking computes `f x`. Needs lazily evaluated values, or a
  translation of `==` that keeps its operands out of types.
- **Unification as a work list**, keeping its constraint order (it has a
  depth guard meanwhile, after step 4).
- **Mutation testing** (in small sharded runs): the machine (`value.rs`),
  `budget.rs`, `native.rs` (167 mutants, never done).
- **Recorded benchmarks** with a regression threshold: the example suite,
  `lengths 400 3000`, text split/join on 10⁴ characters, generated rows.
- **Prove** `textToNat (natToText n) = Just n` (needs lemmas about `/` and
  `%`; tested only, for now).
- **`Partial`** ([proposal](docs/proposals/partial.md)): until it's settled, an
  infinite `Comp` is unsound.
- **Lacks constraints on row variables** aren't enforced (only reachable with
  a hand-written `Sig`).
- **Inferring a bare lambda's type** needs an annotation, e.g.
  `runState ((\n -> n) : Nat -> {Choose} Nat) …`.
- **Forward references and mutual recursion.**
- **Records** (milestone 8).
- **Performance of effectful code** (deep handler trees) hasn't been measured.
- **Namespaces or modules.** Prelude names can't be redefined, so text
  operations are prefixed (`textLength`, `textSplit`) and every new prelude
  name risks clashing with user code.
- **DESIGN.md §16 open questions** that are still open (universes, handler
  admissibility and semantics, effects and dependency, `withFuel`, `Float`,
  the CLI name).

## Known issues

- **A failed declaration stays declared without a body**, so later
  declarations in the same module can use it. Safe only because a module with
  any error is rejected as a whole. Consider removing failed declarations.
- **The machine starts a nested machine** when a native forces an argument
  that's a solved metavariable (elaboration only). Bounded by the term, not by
  program depth, but it's the one exception to "no re-entry".
- **Memory per frame:** a million-deep recursion peaks at about 750 MB; the
  default limit is 2 million frames.
- **Remaining surviving mutants** judged equivalent or unreachable:
  `effects.rs` lines 223 (×3), 403, 414, 706 (×2), 709, 745, 844;
  `termination.rs` line 111 (`>` → `>=`); the `auto` fix in step 1 (masked
  by the sticky budget).

## Recently done

- `5caa024` `unsafe` allowed with a written justification (lint `deny`, was `forbid`).
- `cdfae0d` Stack-safe step 2: the abstract machine, the reference evaluator, differential tests, iterative freeing of values.
- `14ac90d` Every sub-term the evaluator runs is behind its own `Rc`.
- `2942e55` Checking computes an argument only when a type needs it.
- `e53c53f` Stack-safe step 1: resource errors and per-operation budgets.
- `02235d8` Constructor fields shared (fixed quadratic list recursion).
- `0878284` Text step 2: `Text`, its operations and laws, `++`.
- `01313d1` Text step 1: `Char`, literals and escapes.
