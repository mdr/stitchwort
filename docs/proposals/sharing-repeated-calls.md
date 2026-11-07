# Proposal: should the optimiser merge repeated pure calls? (SW-2325)

Status: design note, waiting for Matt's decisions (D3390, D3391). Written 7 Nov 2026 on
`main` at `4baab81a0`, for D3359 in `docs/research/lean-runtime-speed.md` (SW-2318). Nothing
was built or run except `grep` and a small read-only Python script over the `.sw` sources
(§3.3). Labels: **[read]** read in the code or source named, **[cited]** read in a fetched
web page, **[ran]** counted for this note, **[inferred]** my reasoning, **[memory]** from
memory, not re-checked.

## 0. Summary

**The problem, plainly.** Write `Node (Tree.make depth) (Tree.make depth)` and Stitchwort
builds two trees. Lean builds one and points both fields at it, because its compiler
notices the two calls are the same and merges them (common subexpression elimination,
CSE). On the binary-trees benchmark that is the difference between about 68 M allocations
and about 1.5 M (lean-runtime-speed.md §2.1). Merging is legal in pure code: the answer is
the same. But a merged value is *shared*, and Stitchwort's fast paths (reusing a cell in
place, updating an `Array` without a copy) only work on values that aren't shared. So a
merge the user never asked for can turn an in-place update into a copy, or keep a big value
alive across a long computation, and nothing in the source says why.

**What I found.**
- Every system with in-place reuse that I read either doesn't merge calls (Koka, Roc) or
  refuses to merge anything whose result is later updated in place (Futhark). Lean merges
  everything pure, with no reuse check, and its own benchmark suite adds a dummy argument to
  binary-trees "to suppress the common sub-expression elimination optimization" (§1).
- The literature agrees CSE is not "safe for space": it can make a program hold memory for
  much longer, sometimes unboundedly more (§1.8).
- In our own code it would almost never fire. Across the 252 runtime `.sw` files of `aoc/`,
  `bench/compare/` and `games/` (no proofs, specs or tests), the only repeated call that
  builds a new value, in the same scope, is binary-trees' `Tree.make depth` (§3.3)
  **[ran]**.
- Users already have the control: a `let` is computed once, where it's written. `let t :=
  Tree.make depth; Node t t` gets Lean's result in Stitchwort today, on purpose and visibly
  **[inferred from `machine.rs:5-23`, `code.rs:13-29`]**.

**The recommendation.** Option A, with E's documentation: **the optimiser never merges a call
that builds a new value; the user's `let` is how you share.** Document it in the guide's
performance notes. Keep option B (merge only calls whose result can't be updated in place,
such as numbers and booleans) as a possible later stage, behind a measurement of how often
it would fire after inlining. Reject merging everything (C) and a reuse-aware merge (D) for
now (§4).

## 1. What other systems do

### 1.1 Lean 4 (LCNF): merges everything pure, before reuse is decided

- `cse` runs three times: twice in the base phase and once in the mono phase
  (`src/Lean/Compiler/LCNF/Passes.lean:96`, `:115`, `:138`) **[read]**. Reset/reuse is
  inserted later, in the impure phase (`insertResetReuse`, `:146`; `expandResetReuse`,
  `:152`) **[read]**. So reuse analysis sees code that has already been merged, and CSE
  never asks whether the merge will cost a reuse.
- The pass keys a hash map on each `let`'s whole value and replaces a later identical `let`
  by the earlier variable (`CSE.lean:68-83`) **[read]**. Any pure `let` counts: calls,
  constructors, projections. There is no size or cost test. Scopes are respected: each
  `cases` arm starts from its parent's map and its own additions are dropped afterwards
  (`withNewScope`, `CSE.lean:39-41`, `:107-111`), so two calls in different branches are
  never merged **[read]**.
- The only opt-out is `@[never_extract]` on the called declaration, documented as "for
  declarations that have implicit effects that should be repeated"
  (`NeverExtractAttr.lean:15-28`; checked at `CSE.lean:51-56`, `:72`) **[read]**. It is
  about effects, not about memory or reuse.
- A separate pass, `extractClosed` (`Passes.lean:141`, `ExtractClosed.lean`), moves closed
  terms to top-level constants, which shares them for the whole run **[read]**. That's the
  same trade at program scale; our `hoist.rs` refuses it for everything but `SigMap`s
  (§2).
- Lean's own `tests/compile_bench/binarytrees.lean` writes `make' (n d : UInt32)` under the
  comment "This function has an extra argument to suppress the common sub-expression
  elimination optimization" **[cited in lean-runtime-speed.md §2.1]**. So the benchmark
  authors treat the merge as distorting the benchmark, not as a win to show off.

### 1.2 Idris 2: closed terms only, lifted to the top level

`src/Compiler/Opts/CSE.idr:1-27`: "The main goal right now is to move duplicate expressions
introduced during autosearch (which includes interface resolution) to the top level ... it
operates only on closed terms right now, which are ... introduced as new zero-argument
toplevel functions" **[read]**. It notes whether a term was found inside a `Delay` and
treats that case differently (`CSE.idr:93-111`, `:266-271`) **[read]**. It has a `--no-cse`
flag (`src/Idris/CommandLine.idr:259`, `Core/Options.idr:205`) **[read]**. So its target is
compiler-made duplicates (dictionaries), not the user's calls. Idris 2's back ends (Chez,
Racket, JS) are garbage collected, with no in-place reuse of data to break.

### 1.3 Agda: none of its own

Agda's treeless passes (`src/full/Agda/Compiler/Treeless/`: `Simplify`, `Erase`, `Uncase`,
`Unused`, ...) contain no CSE; grep for `cse`/"common sub" in `src/full/Agda/Compiler`
finds nothing **[read]**. Its GHC back end (MAlonzo) emits Haskell, so GHC's CSE applies to
that output **[inferred]**.

### 1.4 Koka (Perceus): no CSE pass

Grep for CSE in `koka/src` finds nothing; the core passes are simplify, inline,
specialise, lift, the FBIP check (`Core/CheckFBIP.hs`) and Perceus's dup/drop and reuse
(`Backend/C/Parc.hs`, `ParcReuse.hs`, `ParcReuseSpec.hs`) **[read]**. I found no stated
reason. Mine **[inferred]**: Koka's `fip`/`fbip` annotations promise that a function runs
in place when its argument is unique (`CheckFBIP.hs:82-84` checks only annotated
functions) **[read]**, and a compiler that introduced sharing could break that promise
after the check. The Koka group also declined to *infer* borrowed parameters because that
"is not safe for space" (in-place-reuse.md §1.3, from Lorenzen and Leijen, ICFP 2022)
**[read there]**, which shows how they weigh space safety.

### 1.5 GHC: CSE and full laziness, both with known memory costs

- `-fcse` is on at `-O`. The user guide's only caveat: "Switching this off can be useful if
  you have some `unsafePerformIO` expressions that you don't want commoned-up" **[cited:
  GHC user guide, Optimisation]**.
- `-ffull-laziness` floats `let`s out of lambdas "in the hope they will be thereby be
  computed less often", and "Full laziness increases sharing, which can lead to increased
  memory residency"; it is "not applied consistently, so don't rely on them" **[cited:
  same page]**. That's design C of compute-once.md §3.3.
- The textbook leak: `avg n = sum [0..n] `div` length [0..n]`. Merged, the list is kept
  whole between `sum` and `length`; unmerged, each is consumed as it's built **[cited:
  haskell-cafe, "Safer common subexpression elimination", Nov 2010]**. In a strict
  language the list is built whole either way, so this exact leak doesn't apply to us; the
  lifetime one in §3.1 does.

### 1.6 OCaml (native back end, Flambda): no CSE of calls or allocations

The back end's `CSEgen` numbers pure arithmetic and loads, but "for function calls" it
forgets everything, and allocations are handled specially, never merged
(`asmcomp/CSEgen.ml`, `class_of_operation`, the `Icall_*` and `Ialloc` cases) **[cited:
source fetched from GitHub]**. OCaml functions may have effects and blocks may be mutable,
so it can't do more. Flambda 2's CSE works on primitives in the same spirit **[memory]**.

### 1.7 MLton: merges constructors and pure primitives, never calls

`mlton/ssa/common-subexp.fun` merges `ConApp`, `Tuple`, `Select` and primitives that are
`Prim.isFunctional` (`:51-98`, `:136-163`) **[read]**. Calls are SSA transfers, not
statements, so they're never merged **[read: the table covers statements only]**. Merging
an immutable constructor is safe in MLton because it is garbage collected and never updates
an immutable value in place.

### 1.8 Roc, Futhark and the literature

- **Roc** (the Zig rewrite, `roc-lang/roc` at `22e0ced`): no CSE in `src/` by grep
  **[read]**. It relies on uniqueness for in-place updates, like us.
- **Futhark** has uniqueness types and in-place array updates, and its CSE is the closest
  precedent for a reuse-aware merge. `Futhark/Optimise/CSE.hs`: a binding whose name is
  later consumed (updated in place) is never merged (`patElemName pe `nameIn` consumed`);
  "It is never safe to CSE arrays in stms in isolation, because we might introduce
  additional aliasing"; and once memory is explicit, arrays aren't merged at all, "since at
  that point arrays have identity" **[cited: source fetched from GitHub]**. Futhark knows
  what's consumed from its type system. We'd have to work it out from erased IR (§4.4).
- **CSE and space.** Chitil, "Common subexpressions are uncommon in lazy functional
  languages" (IFL 1997, LNCS 1467), built CSE into GHC and found the gain small on real
  programs, because such subexpressions are rare, and noted that where a merge leaks space
  it can be cheaper to recompute **[cited: abstract and excerpts only]**. Schmidt-Schauß
  and Dallmeyer, "Space improvements and equivalences in a functional core language"
  (arXiv 1802.06498), classify CSE as a space leak under their space measure, while some
  instances aren't **[cited: summary of the search result; not read in full]**.
  Gustavsson and Sands' space-improvement theory (1999, ICFP 2001) is the framework these
  build on **[cited: abstract]**.
- **"Safe for space"** (Appel, *Compiling with Continuations*, and Shao and Appel's closure
  work) asks that a transformation never make a value live asymptotically longer than the
  source program says **[memory]**. CSE breaks that whenever the merged value would
  otherwise die before a long computation and be rebuilt after it (§3.1).
- **CSE against uniqueness.** In systems where uniqueness is a type (Clean, Futhark, Rust's
  moves), introducing sharing is a type error, so the compiler can't merge a unique value
  **[inferred]**. Systems with a dynamic uniqueness test (Lean, Koka, Roc, us) get no error:
  the program just copies. That's what makes the cost invisible.

**What we learn.** Merging is common where values are garbage collected and never updated
in place (GHC, MLton, Idris 2). Where reuse depends on uniqueness, systems either don't
merge (Koka, Roc), refuse merges whose result is updated (Futhark), or merge blindly and
accept the occasional copy (Lean). The reported gains on real code are small (Chitil), and
the best-known win is a benchmark its own authors disable.

## 2. Where Stitchwort stands

All read from the code at `4baab81a0`.

- **The optimiser merges nothing today.** `crates/rt/src/opt.rs:1-34` lists its rules:
  inlining small non-recursive functions, beta, known constructors, case of case, known
  calls and copies for known function arguments. None compares two expressions for
  equality, and the IR's `Expr` doesn't derive `PartialEq` (`crates/rt/src/ir.rs:203`).
- **It also never duplicates a call on one path.** Inlining binds arguments with `let`s,
  "or substituted when they're variables or constants" (`opt.rs:9-11`), and case of case
  copies code into branches, only one of which runs (`opt.rs:17-19`, `:886-903`). So
  today, the number of times a call runs, and so what is shared, is what the source says.
  That's a property worth naming: *the optimiser preserves sharing*.
- **Known constructors are the nearest thing to CSE.** A `match` on a variable already
  matched by an enclosing arm, or built by a `let`, takes its arm with no test, reusing the
  fields already in hand (`Known::Ctor`, `opt.rs:697-708`, used at `:860-868`). That merges
  repeated *matches*, and is sharing-neutral: the fields were already live.
- **Sharing that exists by design.** A `let` is a register, filled once
  (`crates/rt/src/machine.rs:5-23`). A top-level constant is computed when first used, then
  kept (`machine.rs:21`). `hoist.rs` builds each closed `SigMap` once, and refuses anything
  else, "since hoisting an arbitrary closed term (a long `List.range`, say) would keep its
  value alive for the whole run" (`crates/rt/src/hoist.rs:15-19`). `Array.empty` is a
  constant every use shares, which costs nothing to copy (`crates/rt/src/prims.rs:841-842`).
- **How sharing meets reuse.** `code.rs` moves a value on its last use and, when a matched
  cell is unique, takes its fields out and keeps the cell as a reuse token for the next
  constructor of the same arity (`crates/rt/src/code.rs:13-29`). The test is dynamic: "A
  cell that is shared is never changed: its fields are copied and it's left alone"
  (`code.rs:26-27`; `strong_count == 1`, `machine.rs:1489`). `Array.set` and friends copy a
  shared buffer and count the copy (`unshared`, `prims.rs:838-856`). So a merge never gives
  a wrong answer here; it can only turn reuse into allocation and in-place updates into
  copies, and keep values alive longer.
- **Steps and limits.** Machine and native run the same bytecode, so any `opt.rs` pass
  changes their step counts identically, and D1253 (limits hit at the same point on both)
  holds **[inferred from `crates/native/src/lib.rs:1-12`]**. JS lowers separately
  (compute-once.md §2), so a pass in `opt.rs` wouldn't reach it.
- **Effects are values in the IR.** "A partial computation is a value until the runner runs
  it" (`opt.rs:30-31`), and effect operations are `PrimOp::Effect` (`ir.rs:309-312`).
  Merging two identical effectful computations would be sound in principle (running the
  shared computation twice still performs both), but I'd exclude `Effect`, `Delay` and
  `Hole` prims from any merge, as Lean's `never_extract` does, rather than lean on that
  argument **[inferred]**.

## 3. What a merge costs here: three examples

### 3.1 Memory kept alive across a recursive call

```
def walk: Nat → Nat
  | Zero => 0
  | Succ k =>
    let before := (Tree.make 16).check
    let rest := walk k
    before + rest + (Tree.make 16).check
```

As written, each level builds a tree, checks it (which frees it as it goes, since `check`
consumes its argument), recurses, then builds and checks another. Peak memory is one tree
plus the stack. Merged, the tree built at each level stays alive across `walk k`, because
the second use needs it: peak memory is *k* trees, about 130 k cells each. With `k = 1000`
that's 130 M cells instead of 130 k **[inferred]**. This is the "safe for space" failure,
and the user can't see it in the source.

### 3.2 An in-place update that becomes a copy

```
let a := (List.range 0 n).map double
let b := (List.range 0 n).map triple
```

As written, each `map` takes a fresh, unique list and refills its cells in place (the
`Unpack`/`CtorReuse` path), so the two lines allocate `n` cells each, for the two ranges.
Merged, the range is shared: the first `map` sees shared cells and allocates `n` new ones,
and the second, now the last user, reuses. Total allocation is the same, but peak memory
goes from `n` to `2n`, and the reuse report planned in SW-1810 would show a "shared
Unpack" at a site where the user wrote nothing shared **[inferred from `code.rs:13-29`]**.
With `Array`, the copy is counted against the user's `Array.set` by `prims.rs:838-856`.

### 3.3 How often it would fire in our code

I scanned the runtime code for repeated calls **[ran]**:
- Files: the 654 `.sw` files under `aoc/src`, `bench/compare` and `games` (no Lean ports),
  less those under `Proofs/` and `Spec/`: 252 files. Proofs are erased, so their repeats
  don't run.
- Same line, qualified call with arguments, repeated (`grep -P`): 4 hits. Binary-trees'
  `Node (Tree.make depth) (Tree.make depth)` (`bench/compare/binary-trees/main.sw:10`);
  `Mod.size n` three times (`aoc/src/Aoc/Year2025/Day01/Day01.sw:87`), a number; and two
  test lines whose calls differ.
- Same definition, a bracketed application repeated (a Python script over each definition
  body, tests excluded): 27 hits. Apart from binary-trees, every one is a type, a small
  constructor (`(X bit)`, `(Cons True)`), a call in two different `match` arms
  (`aoc/src/Aoc/Common/Elimination.sw:32` and `:36`; `Year2024/Day17/Day17.sw:124`, `:126`,
  which a scoped CSE wouldn't merge anyway), different variables with the same name
  (`Year2021/Day16/Day16.sw:105-106`, `char` inside and outside a lambda), or `middle.drop
  1` (`Year2024/Day04/Day04.sw:65-66`), which allocates nothing.
- Same line, a dotted name repeated: 167 hits, almost all field reads (`to.row`,
  `from.column`), which merge nothing: our field reads are `match`es that known
  constructors already handle (§2).

So in the source, the one allocating repeat is the benchmark. What the scan can't see is
repeats that only appear **after inlining** (two inlined helpers that each compute
`xs.length`, say). Those would mostly be numbers, which is option B's territory, and need
a count from the optimiser itself (ticket 3).

## 4. The options

Each is judged on: what users get, what it costs, what it rules out, what it does to real
programs and to benchmarks, and whether users can predict the cost of their code.

### 4.1 A. None: the optimiser never merges calls

**Change.** Nothing in the optimiser. State the rule (the optimiser preserves sharing) in
`opt.rs`'s header and the guide.

- **Real programs:** no change; nothing in the corpus loses (§3.3).
- **Benchmarks:** binary-trees keeps building `2^(depth+1) − 1` nodes, like CPython and
  like Lean once its port is fixed (SW-2319).
- **Predictability:** best. "Each call runs; a `let` shares" is a rule a user can apply by
  reading the code, and it's what the reuse report (SW-1810) and the array-copy counter
  assume.
- **Rules out:** wins from compiler-made duplicates after inlining. Likely small (§3.3), but
  unmeasured.

### 4.2 B. Merge only calls whose result can't be updated in place

**Change.** A CSE pass in `opt.rs`, after inlining, that merges two identical pure
expressions in the same scope (the first dominates the second) only when the result is a
*small immutable value*: a `Prim` returning `Nat`, `Int`, `Bool`, `Char` or `Float`, a
literal, or a call of a function that only returns such values. That last needs a small
"returns a scalar" fixpoint over globals, since types are erased before this IR
(lean-runtime-speed.md §4). Exclude `Effect`, `Delay` and `Hole` prims.

- **Why it's safe:** a small number has no cell to reuse, and keeping it alive costs a few
  words. The merge is sharing-neutral. A big number (`BigNat`) is heap-held but never reused
  (in-place-reuse.md §1.2: "big numbers are never reused"), so only its lifetime changes;
  I'd include it, since the result of `Nat` arithmetic can't be told apart from a small one
  at compile time **[inferred]**.
- **What it gives:** fewer steps for repeated arithmetic after inlining, such as `Mod.size
  n` (Day01.sw:87) or a `length` two helpers each compute. Probably a few percent at best on
  a handful of days **[inferred; unmeasured]**.
- **Costs:** an expression-equality and hashing over the IR (it has neither today), the
  scalar classifier, about one Opus lane. It shares the classifier with compute-once.md's
  C-narrow hoisting (§3.3 there, rule 3), which needs the same "small immutable value"
  test: build it once for both.
- **Predictability:** good. Merging numbers can't change memory behaviour, so the user's
  model ("a call is a call") stays right for everything that costs memory.
- **Rules out:** nothing for later.

### 4.3 C. Merge everything pure, as Lean does

**Change.** Merge any identical pure `let` or call in scope, as `CSE.lean` does.

- **Benchmarks:** binary-trees allocates `depth + 1` nodes per tree, as Lean's unfixed port
  does. Our `check` would then increment fields of shared cells instead of freeing them,
  still visiting every node.
- **Real programs:** no gain found (§3.3). The cost is the §3.1 and §3.2 kind: unbounded
  extra memory in the worst case, lost reuse and array copies in the common one.
- **Predictability:** poor. Whether two calls merge depends on whether they're identical
  *after inlining*: `make d` and `make (d + 0)` differ, two inlined helpers may collide.
  An array update can start copying because of a change in another function. And it
  undermines anything we later promise about in-place code (a Koka-style `fip` check would
  have to run after CSE, or be broken by it).
- **Rules out:** a dependable reuse story, which in-place-reuse.md's plan is built on.

### 4.4 D. Merge with a reuse-aware check (Futhark's rule)

**Change.** Merge an allocating call only when no use of the merged value consumes it: no
use reaches an `Unpack` that claims a token, an `Array` update, or a function that does
either; and the value doesn't live across a call it would otherwise die before (§3.1).

- **What it gives:** binary-trees' speed-up (`check` only reads), with no reuse lost.
- **Costs:** an interprocedural consumption analysis over erased IR (Futhark gets it from
  types), plus a liveness test against calls. Two to three Opus lanes, and tests for each
  negative case. It overlaps borrowed-parameter inference, which in-place-reuse.md left
  until measured (SW-1811): "does this function only read its argument?" is the same
  question.
- **Real programs:** nothing in the corpus would merge (§3.3).
- **Predictability:** middling. The merge is invisible but can't cost memory, provided the
  analysis is right; when it's wrong, the failure is the silent kind.
- **Rules out:** nothing, but it's a large, subtle analysis for one benchmark.

### 4.5 E. The user decides: `let`, plus help noticing

**Change.** No new language. The user writes `let t := Tree.make depth; Node t t` when they
want sharing, which already works (§2). Add:
- a guide bullet in "Performance notes" (`docs/guide/11-running-and-shipping.md:160`):
  each call runs, a `let` shares, and a shared value can't be updated in place;
- optionally a hint: the profiler hint planned in compute-once.md stage 0b (a function
  called many times on the same arguments) already covers "the same call twice"
  dynamically. I'd not add a separate lint, since §3.3 found nothing for it to flag.

An annotation (`@[cse]` on a definition, or a `share` expression) is the other form of E.
I don't recommend it: `let` already says "compute once" in the language everyone reads, and
an annotation would be a second way to say it that only the optimiser understands.

- **Predictability:** best, same as A.
- **Costs:** a DeepSeek-sized guide change.

### 4.6 Side by side

| Option | Real programs | binary-trees | Memory risk | User can predict | Cost |
|---|---|---|---|---|---|
| A none | no change | 2^(d+1) nodes | none | yes | nothing |
| B scalars only | small, unmeasured | no change | none | yes | 1 Opus lane |
| C all pure (Lean) | no gain found | d+1 nodes | unbounded (§3.1) | no | 1 Opus lane |
| D reuse-aware | none found | d+1 nodes | none if correct | partly | 2-3 Opus lanes |
| E `let` + docs | user's choice | user's choice (`let`) | user's choice | yes | 1 DeepSeek lane |

## 5. Recommendation

**A + E now; B later, only if a measurement shows it pays.** The optimiser never merges a
call that builds a new value, and that rule is stated in `opt.rs` and the guide. Sharing is
the user's to ask for, with a `let`.

Why: the merge's one known win is a benchmark artefact (Lean's own suite disables it), the
corpus has no other case, and its costs fall on exactly what Stitchwort is building towards
(in-place reuse, array updates, a reuse report users can trust). Keeping "the optimiser
preserves sharing" as an invariant is cheap now and expensive to win back later. B is
harmless and keeps the door open for the inlining-made duplicates the grep can't see.

**What would change this:**
- The optimiser count (ticket 3) finds repeated scalar expressions after inlining in hot
  code of several days: do B.
- It finds repeated *allocating* calls after inlining in real days, costing (say) over 5%
  of a day's allocations: revisit D, after borrowed-parameter inference (SW-1811) exists to
  answer "only read".
- Matt decides benchmark parity with unfixed ports matters: it shouldn't, since SW-2319
  fixes the port the way Lean's own suite does.

**Calls I made** (implementation, reversible):
- B, if built, runs in `opt.rs` after inlining (where duplicates appear), dominating
  occurrences only (no merging across `match` arms, as Lean's `withNewScope`), and excludes
  `Effect`, `Delay` and `Hole` prims.
- B includes big numbers (their lifetime changes, not their reuse).
- The scalar classifier is shared with compute-once.md's C-narrow, whichever lands first.
- No separate "repeated call" lint; compute-once.md's profiler hint covers the dynamic case.
- The measurement comes before any B implementation.

## 6. Questions for Matt

- **D3390: May the optimiser change what is shared, by merging calls that build new values
  (lists, trees, arrays, records)?** [rec: no, as a standing rule ("the optimiser preserves
  sharing"). Its only known win is a benchmark artefact, nothing in our code would merge,
  and it silently breaks in-place reuse and can hold unbounded extra memory. Merging
  results that can't be reused (numbers, booleans) stays allowed.]
- **D3391: Is `let` the user's control for sharing, with no annotation or new syntax?**
  [rec: yes. `let` already means "computed once, here", it works today
  (`let t := Tree.make depth; Node t t`), and a second spelling would only exist for the
  optimiser. Document it in the guide.]

## 7. Tickets to file

In order. 1 and 2 can run in parallel; 3 gates 4.

1. **[DeepSeek, 20 min] State "the optimiser preserves sharing" in `crates/rt/src/opt.rs`'s
   header** (after the "Everything here is pure and total" paragraph, `opt.rs:30-34`): it
   never merges two calls and never runs a call more often on one path, so what is shared
   is what the source says (D3390). Comment only. *Tests:* none needed beyond `cargo fmt`
   and clippy on the file; no test run.
2. **[DeepSeek, 30 min] Guide: "A call runs each time; a `let` shares"**, a bullet in
   `docs/guide/11-running-and-shipping.md`'s Performance notes, with the binary-trees
   example and one line on why a shared value can't be updated in place. Can merge into
   compute-once.md's stage 0a ("Keeping a derived value") if that lane hasn't run.
   *Tests:* the guide example check (`crates/cli/tests/tools/guide.rs`) via `task test:one`.
3. **[Sonnet, 45 min] Measure: repeated pure expressions after `opt.rs`**. A debug-only
   counter (an env var, or a test helper over `optimize`'s output) that, per body, counts
   pairs of identical pure expressions where one dominates the other, split into scalar
   results, constructors and calls of allocating functions, with the global's name. Run it
   when *lowering* (not running) a sample of ten AoC days and `bench/compare`; record the
   counts in this note's §3.3. *Tests:* a unit test of the counter on a small IR body; the
   sample is lowering only, about a minute. Lowering the whole of `aoc/` is a broader run:
   the orchestrator asks Matt before allowing it.
4. **[Opus, 75 min, only if 3 shows repeats in hot code] B: CSE of scalar-result pure
   expressions in `opt.rs`**, with the "returns a scalar" fixpoint shared with
   compute-once.md's C-narrow (SW-2027, or whichever ticket holds C-narrow). *Tests:* unit
   tests of the pass, one per negative case (an allocating call, a call under a different
   arm, an `Effect` prim, a variable bound between the two); `task test:one` on the days
   ticket 3 found, comparing steps before and after.

Existing tickets: SW-2319 (fix the Lean binary-trees port) is the measurement fix and needs
nothing from this note. SW-1810 (reuse columns in `--profile`) is the diagnostic that would
show a merge's cost if one were ever added; this note adds a reason to do it, no change to
it. D3359 is answered by D3390.

## 8. What I didn't cover

- I didn't read Chitil's or Schmidt-Schauß's papers in full; their claims here are from
  abstracts and summaries.
- I didn't read Flambda 2's CSE, GHC's `CSE.hs` notes, or Roc's older Rust compiler.
- The corpus scan is textual: it misses repeats spread across lines in other forms, and
  everything inlining creates (ticket 3 covers that).
- I didn't look at JS: a merge in `opt.rs` wouldn't reach it, and its values are garbage
  collected, so it has no reuse to lose.
- Top-level closed-term extraction (Lean's `extractClosed`, Idris 2's CSE) is the same
  trade at program scale; `hoist.rs` already refuses it outside `SigMap`s, and I didn't
  re-argue that.
