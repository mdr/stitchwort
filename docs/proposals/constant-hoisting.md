# Closed expressions computed once (SW-2497)

SW-2497, 9 Nov 2026, Opus, paper lane on `lane/SW-2497` from `main` at `ae065eb64`. Nothing was
built or run: the code was read, and the counts come from earlier profiles. Labels: **[read]**
seen in the code (file:line), **[measured]** from a profile or run someone made and wrote up
(named), **[inferred]** worked out from the code, not run, **[estimated]** a guess at an effect,
with how it was made.

Builds on [compute-once.md](compute-once.md) (SW-2014: what the runtimes do today, §2, and
C-narrow, §3.3), [sharing-repeated-calls.md](sharing-repeated-calls.md) (SW-2325: why we don't
merge repeated calls) and [parse-runtime.md](parse-runtime.md) (SW-2327, whose option B assumed
"with constants hoisted, `"mul(".toList` is computed once", line 252, which nothing built). The
numbers are SW-2492's (`docs/reviews/SW-2492-expressions-scan-profiles.md`).

## 0. Summary

**The problem, for a user.** `Parse.text "mul("` turns `"mul("` into a list of characters every
time it runs, and `Parse.pick [("do()", Do), ("don't()", Dont)]` does the same for each word on
every try. On the `scan` benchmark (AoC 2024 day 3) that is 6.02 M conversions, on
`expressions` (2020 day 18) 3.28 M **[measured, SW-2492 §1.3, §2.3]**. Writing the lists as
top-level constants by hand saved 5.8% and 3.9% of all instructions **[measured, SW-2492
target 4]**. Nobody should have to do that: the value can't change, so the compiler should
compute it once. The same is true of any expression that uses no variables, in any program.
SW-2494 showed std alone can't fix it (a `Parse` operation over `Text` cost as much as the list,
**[measured]**).

**The change.** Three pieces, in the order they'd be built:

1. **Fold literal conversions in the optimiser** (`opt.rs`): `Text.toList` of a text literal
   *is* a character-list literal, and the IR already has one (`Lit::Chars`) that the bytecode
   compiler builds once into its constant pool (`code.rs:790`) **[read]**. Also pool
   constructor trees built only from literals (`[("do()", Do), …]`), which are allocated on
   every evaluation today (`code.rs:858-887`) **[read]**.
   **And build each capture-free lambda's closure once**: a `Closure` with no captures
   allocates a new function value every time it runs (`machine.rs:1311-1317`) **[read]**;
   `Parse.optional` builds nine of them each time it starts a handler, at about 159
   instructions each **[measured, SW-2493 §2.3, §7.4]**. This is the same rule (a lambda
   with nothing free is a closed expression) and the biggest single piece of it.
2. **Float closed expressions to module constants** (a new pass after `opt.rs` simplifies a
   body): an expression in a function or lambda that reads no variable becomes a constant,
   **computed the first time that expression is reached and kept if its value is small**
   (at most 128 cells, say); a bigger value is not kept, and is computed each time, as today.
   Because it runs exactly where and when the original first ran, and pure code can't tell the
   difference, nothing new can loop, fail or cost more; the only new cost is the memory of the
   kept values, which the size limit bounds. This is the general fix: it needs no knowledge of
   `Parse`.
3. **Later, and only if measured worth it:** copies of a recursive function for a small literal
   list it's given (so `List.find` over `pick`'s two words unrolls and both lists become
   literals), and a faster native read of a constant.

**What it should do.** Capture-free closures alone: 3.5 to 3.9% fewer instructions on
`expressions` and 2.6 to 3.1% on `scan`, and something for every program that passes lambdas
**[estimated by SW-2493 §7.4 from a measured 159 instructions a closure and static counts]**.
The literal conversions on top of that, on `scan`: 3 to 5% after pieces 1 and 2, 5 to 7% with
piece 3 **[estimated from the measured 5.8%, split by where the conversions happen (§6)]**. On
`expressions`: 0.5 to 1.5% **[estimated]**, and up to about 5% only if the optimiser's existing
copies for known constants reach Day18's operator lists, which I couldn't check without running
it (§6.2). In other programs: every parser with a literal (`char ','`, `text ": "`, `pick
[…]`, 96 such call sites in `aoc/`, §6.3) gets cheaper, by a few percent of its parsing time;
code with no closed expressions is unchanged.

**Decisions for Matt** (§9): adopt the rule "an expression that uses no variables is computed
at most once per run, if its value is small" as the end state (D3438), and say so in the
guide's performance notes (D3439). The D numbers are provisional.

## 1. What exists today

All **[read]**.

- **The pipeline.** `lower_roots` (`crates/rt/src/lower.rs:83-195`) lowers each used definition
  to the erased IR (`ir.rs`): a definition with runtime parameters is a
  `GlobalKind::Function`, one without is a `GlobalKind::Constant` "computed when it's first
  used, and kept" (`ir.rs`, `GlobalKind`). Then `optimize` (`opt.rs`), `sums::apply`,
  `trmc::apply`, `reuse::apply`, and `validate` (`lower.rs:188-194`). The bytecode compiler
  (`code.rs`) compiles each body; native code (`crates/native/src/n1.rs`) compiles the same
  bytecode, so whatever the IR passes do, native gets. JS lowers core terms separately and
  shares only erasure, `specialise.rs` and `hoist.rs` with the machine.
- **Constants (CAFs).** The machine reads a constant with `Instr::Global`: if its slot in
  `st.globals` is filled it clones the value, else it pushes a frame for the constant's code
  with `Ret::Const`, whose return fills the slot (`machine.rs:1114-1128`, `:1015-1022`). Native
  code does the same through a helper call `global` on every read and a cold block that
  computes it and calls `global_set` (`n1.rs:3914-3954`). A first use counts one step.
- **The constant pool.** `Expr::Lit` values, including `Lit::Chars` (a text literal's
  characters as a `List Char`), are built once when the body is compiled and read with
  `Instr::Const`, which clones a pool entry (`code.rs:784-795`, `machine.rs:1106`; natively a
  pointer copy and count increment, `n1.rs:3539-3555`). `Lit::Chars` comes only from a
  `Term::Chars` in the core term (`lower.rs:765`); nothing turns a `Text.toList "…"` into one.
  A standalone native executable carries the pool as data trees of literals (`linked.rs:22-24`,
  node kinds `:177-187`): no closures.
- **The one hoist.** `hoist.rs` makes a closed application whose result is a `SigMap` into a
  constant, at lowering time on core terms, so JS shares it (`lower.rs:884-910`). Its comment
  keeps the general case out on purpose: "hoisting an arbitrary closed term (a long
  `List.range`, say) would keep its value alive for the whole run" (`hoist.rs:15-19`).
- **The optimiser.** Inlines a non-recursive function whose simplified body has size at most
  24 (`opt.rs:49`, `:184`), substituting arguments that are variables or constants and binding
  the rest with `let`s; `size` counts a closure as its captures only (`opt.rs:309-331`), so a
  function that builds a computation with a continuation lambda is small. A closure that
  captures constants gets its own lambda with them substituted; a recursive function called
  with a known function or a constant known constructor gets a copy, at most 64 copies of at
  most 200 nodes (`opt.rs:55-57`, `:1225-1260`), but not when *every* argument is known
  (`opt.rs:1244`). Its only constant folding is `Nat` arithmetic on literals (`fold`,
  `opt.rs:793-818`) and `Text.fromList (Text.toList t)` → `t` (`prim`, `opt.rs:1532-1538`).
  It has no CSE and no let floating (compute-once.md §2).
- **Effects are values.** An operation is a `Call` node, `bind` a native that calls the
  continuation when its first argument is `Done` and otherwise builds a `Bind` node
  (`effect.rs:1-33`). Evaluating any IR expression never runs a handler and never does IO:
  only the run loop and the runner do. Operations in place, which would have run handler
  clauses where an operation is evaluated, stopped after stage B (D3430); stage B only skips
  forwarding clauses inside the run loop. This is what makes floating sound (§3.2), and the
  rule to keep if in-place performs ever return.
- **Std.** `Parse.text expected` is `if Parse.literal expected.toList then () else …`, and
  `Parse.pick choices` is `choices.find (choice => Parse.literal choice.fst.toList)`
  (`crates/elab/src/std/Parse/Parse.sw:223`, `:330`). `Parse.char expected` builds its failure
  message `"'${expected}'"` on every call, needed or not (`:217-220`).

## 2. Where it goes

```
core terms ─ lower.rs ─▶ IR ─ opt.rs: inline, known constructors, copies ─▶
    [1] literal folds (inside opt.rs's simplifier)
    [2] float closed expressions (new float.rs, last step of each body)
  ─▶ sums ─▶ trmc ─▶ reuse ─▶ code.rs  [1b] closed literal data → pool
  ─▶ machine / native (constant read: keep if small)
```

**On the IR, after inlining, not on core terms.** The closed expression we want often exists
only after `opt.rs` has inlined a small function at a call site with a literal: in the
library, `expected.toList` reads a parameter. Lowering-time hoisting (where `hoist.rs` lives)
would see `Parse.text "mul("` as a closed *call*, which also works for that case (§4), but it
would miss every closed expression that inlining exposes, and it would hide calls from the
optimiser's own folds (`toBool (decEq 3 4)` would become a constant instead of `False`). The
cost is that JS doesn't share it. compute-once.md chose one shared pass so the backends agree;
here they agree on every answer and differ only in speed, and JS is the playground's backend,
not the benchmarks'. I'd give JS the literal folds (cheap, stage 5) and nothing more until a
web program needs it. That is an implementation call, recorded here.

**Last in each body.** The floating runs on each global's and lambda's body after `opt.rs` has
simplified it, before its inlining snapshot (`opt.rs:184`) is taken. So a closed expression in
a small callee is floated once, in the callee, and every inlined copy shares the one constant;
and a call site's own closed expressions (exposed by inlining there) are floated in the caller.
Identical closed expressions anywhere in the program share one constant, keyed by the
expression as `hoist.rs` keys maps (`lower.rs:896`).

**Not in run-once bodies.** The entry and constants' own bodies run once, so floating out of
them only adds a global. They're skipped.

## 3. Which expressions qualify

### 3.1 Closed

An IR expression is closed when it reads no `Local` or `Captured` value: it's built from
literals, globals (whose values are themselves closed), constructors, closures and partial
applications of closed values, calls, natives and applications of closed values. The pass
floats **maximal** closed expressions: the largest closed expression containing the one it
found, so `text "mul("`'s whole computation goes, not only its list. It leaves alone what is
already a constant or costs nothing to make: a literal, a global, `Erased`, `DoneK`, a
constructor without fields.

### 3.2 Pure: evaluation that can't tell when it ran

Floating moves *when* a value is made, so it's sound only if evaluating the expression has no
effect and gives the same value whenever it runs. In this IR both hold **[inferred from
`effect.rs:1-33` and `opt.rs:29-31`]**:

- a closed expression reads no variable, and globals are closed constants, so its value is
  fixed by the program text: not by the input, nor by the run;
- operations and IO are values (`Call` nodes) until the run loop or the runner takes them
  apart, so building one twice or once is the same; a computation value can be run any number
  of times (resumptions are multi-shot, `effect.rs:23-26`);
- `Partial` computations are `Delay` values until the runner steps them;
- the only mutation is in place on values nothing else holds (reuse tokens, consuming `Array`
  natives), and a kept constant is always held by the globals table, so it is never changed in
  place: a consumer copies instead (§5).

The one thing that would break this is a construct whose evaluation consults run-time context:
an operation performed in place (operations-in-place.md §2.4, dropped by D3430), or any future
native that reads the handler stack. The pass's closedness test must treat such a construct as
reading a variable. Today there are none.

### 3.3 Terminating, and its cost

The worry with hoisting is computing something the program wouldn't have: a loop, a resource
error, or a huge value, in code that never ran. **Computing the constant at its first use, not
at load, removes that worry**: the constant is evaluated exactly where, and when, the original
expression was first evaluated, and later reaches read the kept value. So:

- **It can't loop where the original didn't.** (Stitchwort's runtime code is total anyway: a
  definition that isn't checked can't run, `lower.rs:122-131`; a `decreasing` run body drops
  only the fuel, `globals.rs:106-114`. But the argument doesn't depend on that.)
- **It never does more work.** An expression reached *k* ≥ 1 times costs once instead of *k*
  times; one never reached costs nothing. Under a branch or inside a lambda makes no
  difference, so unlike C-narrow (compute-once.md §3.3, rule 2) there's no "evaluated on every
  call" condition.
- **Steps go down, never up.** The first evaluation counts one more step (the constant's
  frame) and one more frame on the stack, which can move a frame-limit error by one frame.

Evaluating at load time instead (as Haskell's static data, or an eager module initialiser)
would run code the program might never reach, in a different order: rejected. Evaluating at
compile time is what the literal folds do (§4.1), for the cases where the value is known
without running anything.

### 3.4 Size: what is kept

What hoisting can make worse is memory: a kept value lives for the rest of the run. `List.range
0 10_000_000` inside `main` is closed, and today it becomes garbage as `sum` walks it; kept, it
would hold hundreds of megabytes, and the `map` after it couldn't reuse its cells. So:

- **A computed constant is kept only if its value is small**: at most `KEEP` cells, counted
  by walking the value (constructor fields, a closure's captures, a partial application's
  arguments; a `Text` or array as its length over the words of a cell; a big number by its
  words), stopping as soon as the count passes `KEEP`. Values are acyclic, so the walk ends.
  If it's bigger, the constant is marked "not kept" and every later reach computes it again,
  as today, without walking. The value of a closed expression is fixed, so the decision is the
  same on every run and in both backends.
- **`KEEP` = 128 cells** (about 4 KB) is my starting point: `text "mul("`'s computation is
  about 15 cells **[inferred: `Bind`, `Call`, two or three row injections, four list cells, the
  continuation closure]**, a small table up to 128 entries fits. The total kept is at most
  `KEEP` times the number of floated expressions, and in practice far less. The number is an
  implementation constant, tuned by measurement.
- **Values built from literals alone are kept always**: their size is the size of the source
  (a list literal, a closure that captures nothing, §4.3). These need no walk.

This is the only new condition, and the reason the other systems that float to the top level
are criticised (GHC's full laziness leak; sharing-repeated-calls.md §1.8) is the one it
addresses.

## 4. The four kinds, and how each is evaluated

| Kind | Example | Evaluated | Kept |
|---|---|---|---|
| **Folded** | `Text.toList "mul("`, `Text.length "abc"`, `"ab" ++ "c"` | at compile time, by `opt.rs` | as a literal in the pool, always |
| **Capture-free closures** | `optional`'s nine clause lambdas, `c => c == 'x'` after a constant is substituted, `() => Parse.nat()` | once per lambda, when the image is built or at first use | always (one cell each, one per lambda) |
| **Static data** | `[("do()", Do), ("don't()", Dont)]`, `Some 'x'` | constructors of literals: at compile time, into the pool; anything with a closure or a global in it: at first use | always (size is the source's) |
| **Computed** | `text "mul("`, `List.find p [..]`, `List.range 0 8`, `"'${','}'"` | at first use, in its own frame | if at most `KEEP` cells |

### 4.1 Folded

In `opt.rs`'s `prim`/`fold`: `TextToList (Lit::Text s)` → `Lit::Chars s`; `TextFromList
(Lit::Chars s)` → `Lit::Text s`; `TextAppend`, `TextLength`, `TextIsEmpty`, `TextEqual` and
`NatToText` on literals → literals. Folding happens during simplification, so it sees through
inlining and feeds known-constructor and known-literal rules after it. The IR already has the
literal form, the pool already builds it once, and native and standalone executables already
read pooled character lists (`linked.rs:22-24`). The folds return values that are literals of
bounded size (the source's), so there is no size question.

### 4.2 Static data

A closed constructor tree whose leaves are literals is compiled as one pool entry instead of a
chain of `Ctor` instructions (`code.rs`). A reuse token that the constructor would have filled
is then not used by it: the token accounting in `code.rs` (`builds`, `Later::Ctor`) must not
count pooled constructors, or it holds a token for nothing (a missed reuse, not a wrong
answer). Static data with a closure or a global in it can't go in the pool (standalone
executables can't carry closures in it) and becomes an always-kept constant instead.

### 4.3 Capture-free closures

`Expr::Closure(l, [])` reads nothing, so its value is the same function every time; function
values are immutable and nothing can compare them, so sharing one is unobservable. SW-2493 found
these are most of the closures the parsers build: in the 40 hottest bodies, capture-free
`Closure` instructions times their entries are 5.8 M of 9.2 M closures on a tenth of
`expressions` and 6.7 M of 11.2 M on scan's **[measured counts, SW-2493 §7.4; static, so an
upper bound]**; at 159 instructions each **[measured, `next (c => True)` against `next yes`]**
that is the 3.5 to 3.9% and 2.6 to 3.1% above.

They need none of §3.4's machinery: each is one cell, there is at most one per lambda, and
building it runs nothing. So the simplest form is not a constant global but **one shared
closure per lambda**: `code.rs` compiles a capture-free `Closure` as a new instruction that
reads lambda `l`'s static closure from a table the image fills once (or fills at first use, as
a constant is); native code reads the same table. It can't go in the constant pool, because a
standalone native executable's pool holds only data (`linked.rs:177-187`); a table of
lambda numbers rebuilt at start-up works there. More closures become capture-free after
`opt.rs` substitutes constants for captures (`opt.rs:23-25`), so this runs after it, and stage
2's floating makes more still: a closure whose captures are all closed constants is static
data with globals in it (§4.2). Closed partial applications of a global to closed arguments
are the same case and follow it (SW-2493 notes `optional`'s `%elim` one still holds a capture).

One more reason to do these first: they stay sound whatever happens to the effect runtime.
SW-2493 §8 asks Matt to reopen operations in place for native code; if performs ever run
handler clauses where they're evaluated, floating a closed *computation* such as `text
"mul("` would become wrong (§3.2) and that part of stage 2 would have to exclude perform
positions, while a closure, which runs nothing when it's built, is unaffected.

### 4.4 Computed

A new constant global per distinct floated expression, named after where it was found
(`Aoc.Year2024.Day03.instruction[const 0]`, as `hoist.rs`'s are `…[map N]`) so profiles say
what it is. Its kind is `GlobalKind::Constant` with a new flag saying it's kept only if small.
The machine's `Ret::Const` and native code's `global_set` check the flag, walk the value, and
either fill the slot or mark the global as never kept. The walk is one Rust function: native
code's values are the machine's (`n1.rs:3539-3555` clones pool entries of the machine's
`Value`). The codec's and `linked.rs`'s format versions go up for the flag.

## 5. Sharing and reference counts

A kept value is held by the globals table, so every read clones a reference and no reader ever
holds it alone. Two consequences, both bounded:

- **In-place reuse is lost on it.** A `map` over a kept list allocates new cells instead of
  reusing the list's; an `Array.set` on a kept array copies it first. Before floating, the
  same code built the list or array fresh each time, which costs about what the copy costs, so
  this is not the "cliff" of arrays.md §6.1, where a value that was unique becomes shared and
  every update becomes a copy. Here the update was preceded by a build of the same size
  anyway.
- **Memory stays allocated.** Bounded by §3.4.

Pointer identity changes (two reaches now see the same object), which nothing in the language
can observe. The profiler hint compute-once.md §3.1 proposed (distinct first arguments by
pointer) would correctly show fewer distinct values.

## 6. Interaction with inlining, and what each stage reaches

### 6.1 scan: `text "mul("` and `pick`

Per noise character, `findAll` runs one round: `text "mul("` fails (one conversion), then
`pick` tries both words (two) **[measured: 6.02 M conversions for about 1.9 M rounds plus the
matches; SW-2492 §2.4]**. So by count, `text` is a third and `pick` two thirds.

- **`text "mul("`.** `Parse.text`'s lowered body is a `bind` of a `Call` (with
  `Text.toList expected` in it) and a continuation closure, about a dozen nodes with the
  closure counted as its capture, under the inline limit of 24 **[inferred from `opt.rs:309`;
  not checked, see §10]**. Inlined at the call site with the literal substituted, it has
  `TextToList (Lit::Text "mul(")`: the fold (stage 1b) makes that a pooled literal. Without
  inlining, `Parse.text "mul("` is a closed call, so stage 2 floats the whole computation
  instead; evaluated once, it holds the list. Either way, a third of the conversions go.
- **`pick [("do()", Do), ("don't()", Dont)]`.** The call is closed, so stage 2 floats its
  computation. But evaluating a computation only runs it up to its first operation: here,
  `literal` of the first word's list. The second word's `toList` is inside the continuation,
  which runs `find` on the rest of the list each time the first word fails, so it's still
  computed per try. Stage 2 therefore removes the first word's conversions (another third).
  The last third needs the second word to be a literal in the code, which happens if the
  optimiser copies `find`'s predicate-specialised copy for the known two-element list and
  unrolls it (stage 4: specialisation on small closed constructor arguments, today refused
  when every argument is known, `opt.rs:1244`). The alternative is a std change that makes
  `pick` convert all its words before its first operation (`choices.map` first, then a helper
  over the lists); that adds a list of pairs per call where the words aren't closed
  (`expressions`), and touches `pick`'s lemmas (`std/Parse/Runs.sw:648`, `:776`). I'd take
  stage 4, measured first.
- **The rest of the round.** `instruction()`'s whole body is closed, as is each alternative's
  body inside `oneOf`, so stage 2 also floats their computations: the list of two closures
  `oneOf` is given, `oneOf`'s first `mark` node and continuation, and each alternative's first
  `bind` node. About 8 allocations a round **[inferred]**, at the 183 to 229 instructions SW-2463
  measured per removed cell: about 1% of scan **[estimated: 8 × 200 × 1.9 M rounds over 279 G]**.
  Part of this (the capture-free closures) is stage 1a's, so don't add the two.

### 6.2 expressions: `operator`

`operator operators` is `Parse.pick (operators.map (operator => (operator.spaced,
operator)))`, with `operators` one level of `Precedence.levels`, passed down `level`'s recursion
**[read: `aoc/src/Aoc/Year2020/Day18/Day18.sw:79-94`]**. It isn't closed, so stages 1 and 2 do
nothing for its 3.28 M conversions. They become closed only if the optimiser's existing copies
reach them: `parseHomework` is called with the constants `samePrecedence` and `additionFirst`,
whose values are closed constructors, so a copy of `level` for each is possible (`opt.rs`'s
known-argument rule, `:1215-1220`), and inside it `chain [Plus, Times]`, `operator [Plus,
Times]`, and the `map` over a known list. That chain crosses `Parse.recursive`, two closures,
and the inline depth of 12, so whether it fires is a question for the first run of stage 2
**[inferred, not checked]**. If it does, the `map`'s result is floated and, with stage 4,
`pick`'s conversions go too: up to the measured 3.9%. If not, stage 2 still floats `Parse.nat()`
and `Parse.char '('`'s computations and `char`'s message: 0.5 to 1.5% **[estimated: about 1 M
operand attempts a run, 3 to 5 allocations each, plus the message text for brackets]**.

### 6.3 Other code

There are no other profiles that show literal conversions: `TextToList` appears only in
SW-2492 **[grep of `docs/`]**. What the AoC sources have **[ran: grep over the 90 runtime `.sw`
files of `aoc/src` and `games/`, without specs, proofs and tests]**:

- 41 `text "…"` calls in 20 files, 41 `char '…'` in 27 files, 14 `pick [ … ]` in 12 files: all
  closed calls, so stage 2 floats each (and `char`'s message with it). Parsing is a small part
  of most days' run time, so the effect on a whole day is small (under 1% **[estimated]**),
  larger only on parse-heavy days like the two benchmarks.
- 25 `List.range` calls with a literal start, mostly with a variable end (not closed). The
  closed ones (`List.range 0 8` inside a lambda in 2024 day 17) are small and kept: the range
  is built once, and the `map` over it allocates as before.
- Direction lists are already top-level constants (`aoc/src/Aoc/Common/Grid.sw:29`,
  `Plane.sw:102`), which is what users do by hand today.
- The other comparison programs (binary-trees, rbmap, pidigits, spectral-norm, const-fold) have
  no closed expressions in their loops that I could find **[read]**: no change expected.

So the honest summary is: a large gain on parsers that use literals in their hot loop, a small
one on parsing in general, nothing elsewhere, and the cost model becomes one users can rely on
("an expression without variables is computed once").

### 6.4 Code size

Floating makes code smaller (an expression becomes a read of a constant). It changes no inline
limit. Stage 4's copies are the only growth: limited to closed constructor arguments of at most
16 cells and to the existing 64 copies a program (`opt.rs:57`).

## 7. Hashes, caches and counts

- **Kernel hashes and the check cache:** unchanged. All of this is after erasure, on the IR;
  no definition, term or type changes, so definition hashes, `snap:hashes` and the check cache
  keys are untouched.
- **Run-time formats:** the codec (`codec.rs:34`, format 2) and `linked.rs` gain the "kept if
  small" flag, so their format versions go up. Their build hashes already change with any
  change to `crates/rt`, and so do the test cache's keys, so nothing stale is read.
- **Step and effect counts** (what `--profile` and the effect-runtime counters report) go down:
  fewer calls, fewer `bind`s, fewer `Bind` nodes, fewer allocations. Answers don't change.
  Tests that pin exact counts or allocation traces for programs with closed expressions will
  need their snapshots updated; tests that compare machine with native, or either with
  `--reference`, compare answers and are unaffected. Matt already accepted count changes for
  operations in place (D3412: "may change effect and step counts (not results)"); this is the
  same kind of change.
- **User-visible:** `--profile` shows a row per floated constant (`instruction[const 0]`),
  computed once, and lower call counts for `Parse.text` and the like. The cost model a user
  can rely on changes: a guide sentence (D3439). Both are Matt's.

## 8. Stages

Each stage is independently useful and mergeable. Times are lane estimates.

| Stage | What | Model, estimate | Expected effect |
|---|---|---|---|
| **1a** | Capture-free closures built once per lambda (§4.3): a static-closure instruction in `code.rs`, the table in the machine, native code and `linked.rs`. Independent of everything else here. | Sonnet, 60 min | expressions −3.5 to −3.9%, scan −2.6 to −3.1%, every program that passes lambdas gains **[estimated, SW-2493 §7.4]** |
| **1b** | Literal folds in `opt.rs` (§4.1); closed literal constructor trees into the pool in `code.rs` (§4.2). First step: a lowering snapshot of a `text "lit"` call site and of Day03's `instruction`, to confirm what is inlined. | Sonnet, 60 min | scan −1.5 to −2.5% (if `text` is inlined), others ≈ 0 **[estimated]** |
| **2** | `crates/rt/src/float.rs`: maximal closed expressions out of function and lambda bodies into constants (§3, §4.4); kept-if-small flag in the IR, the codec and `linked.rs`; the walk; `Ret::Const` and native `global_set` honour it; names; sharing of identical expressions. | Opus (lowering soundness, native ABI), 120 min | with stage 1b: scan −3 to −5%, expressions −0.5 to −1.5% (more if §6.2's copies fire) **[estimated]** |
| **3** | Guide paragraph (after D3439), in the performance notes of `docs/guide/11-running-and-shipping.md`, with a checked example. | DeepSeek, 20 min | — |
| **4** | Copies of a recursive function for small closed constructor arguments (unrolling over literal lists of at most 16 cells), so `pick`'s second word folds. Only if stage 2's profile shows the remaining conversions are worth it. | Opus, 90 min | scan a further −1.5 to −2% **[estimated: the last third of the measured 5.8%]** |
| **5** | Native constants read without the helper call (an inline load and test), if a profile shows `global` in the hot path; JS gets stage 1's folds. | Sonnet, 45 min | under 0.5% **[estimated]** |

**Relation to SW-2027 (C-narrow, D2883).** C-narrow moves a small value that reads the
enclosing function's variables (`cave.height`) out of a lambda to where the closure is made:
floating to an enclosing scope, not to the top level. It needs the same free-variable analysis
as stage 2. I'd build it in `float.rs` after stage 2, as its second rule, and re-scope SW-2027
to that (orchestrator's call).

### Test strategy

Within the lane budget (targeted runs, each well under two minutes):

- **Stage 1a:** a bytecode test that a capture-free lambda compiles to the static-closure
  read; a test that a closure applied many times and stored in a data structure gives the same
  answers on the machine, `--native` and a standalone `--native` build (the `linked.rs` table);
  the alloc-trace tests (`crates/rt/tests/it/alloc_trace.rs`) updated for the closures no
  longer allocated; `task test:lane AREA=rt` and `AREA=native`.
- **Stage 1b:** unit tests of each fold (positive, and a negative: `toList` of a variable stays
  a call); a lowering snapshot in `crates/rt/tests/it/lower.rs` of a small program with
  `Parse.text "ab"`, showing the pooled literal; `task test:lane AREA=rt`.
- **Stage 2:** lowering snapshots for: a closed call floated; two identical closed expressions
  sharing one constant; an expression reading a variable not floated; nothing floated out of
  `main` or a constant. Behaviour tests (`examples/extract/closed-constants.sw` with `-- run:`
  cases on the machine, `--native` and `--js`, compared with `--reference`):
  - a closed expression under a branch that is never taken, which would exceed the test's step
    limit if evaluated: the run must succeed (laziness);
  - a closed `List.range 0 1000` reached 1,000 times: not kept (an allocation or step counter,
    `crates/rt/tests/it/tick_counts.rs` style, shows it computed each time); a closed
    `List.range 0 8` kept (computed once);
  - a kept array updated with `Array.set` in a loop: right answers (it is copied, not changed);
  - a closed computation run many times (`text "x"` in `Parse.many`): right answers and parse
    errors unchanged (std's `Parse` tests by `task test:one -- Parse`).
- **Effect on the benchmarks:** `--profile` call counts of `TextToList` on scan and expressions
  with a small `repeat` (counts scale with the input), which takes seconds; the full
  instruction counts of `bench/compare` are the orchestrator's (verifier or compute mode), not
  the lane's.

## 9. Decisions for Matt

- **D3438: Is "an expression that uses no variables is computed at most once per run, at its
  first use, and kept if its value is small" the compiler's rule (stages 1 and 2)?** [rec: yes.
  It's the general fix the benchmarks point at, it helps any program with such expressions, it
  can't change an answer, loop, or do more work, because the value is computed exactly where it
  was first needed; the one risk, memory, is bounded by the size limit. The alternative is
  leaving users to write top-level constants by hand, as Day03 would have to.]
- **D3439: Say so in the guide's performance notes, as something users can rely on?** For
  example: "An expression that uses no variables, such as `"mul(".toList` or `Parse.text
  "mul("`, is computed the first time it runs and then reused, unless its value is large. A
  `let` outside a loop still shares a value that depends on a variable." [rec: yes, with
  "large" left unquantified, so the limit can be tuned. It tells people they needn't hoist
  literals by hand, and it is part of how fast their code is.]

D3438 covers the capture-free closures too (they are the same rule, and stage 1a is the first thing to build); they need no decision of their own, since nothing a user sees changes but speed and counts.

Not for Matt, recorded as calls on the ticket: machine and native first, JS only the folds
(§2); `KEEP` = 128 cells to start (§3.4); stage 4 instead of a `pick` rewrite (§6.1);
C-narrow as `float.rs`'s second rule (§8).

## 10. What I didn't check

- **Whether `Parse.text` is inlined at Day03's call site today.** Inferred from the inline
  limit and how `size` counts closures; nothing printed the IR. If it isn't, stage 1b alone
  doesn't help `text` and stage 2 does the work (as a floated closed call). Stage 1b's first
  step checks it.
- **Whether `opt.rs` reaches Day18's operator lists** (§6.2). That decides whether expressions
  gains about 1% or about 5%.
- **The cost of native code's helper call per constant read** against what it replaces. I
  expect a read to be far cheaper than the 1 to 2 K instructions of a conversion (SW-2494's
  measured cost of a walk of the same length), but a constant read in a tight loop of cheap
  work could lose a little; stage 5 is there for that.
- **The size of the computations stage 2 keeps** (§3.4's 15 cells is inferred).
- Profiles of other AoC days: there are none with call counts of closed expressions, so §6.3 is
  from the source, not measured.
