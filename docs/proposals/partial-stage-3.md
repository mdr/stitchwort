# Proposal: `Partial`, stage 3: partial callbacks through the one `List.map`

**Status:** approved as D1213–D1220. Lane 3a (library and elaborator) built,
§10 "As built"; 3b–3e to come.

It follows [partial.md](partial.md) (stage 1: `Delay`, ticks, §7.3's
callback restriction, §10.7's "partiality polymorphism") and
[partial-stage-2.md](partial-stage-2.md) (§4's stage-3 outline, gap G3,
§6 "As built"). It builds on the effect-polymorphic library
([effect-polymorphism.md](effect-polymorphism.md), D1110: one `List.map`
that is fast, stack-safe and provable) and its runtime
([effect-runtime.md](effect-runtime.md), D1162). It also covers D1182:
making partial calls cheaper, which was deferred to this stage.

Claims are marked like this:
- **[ran]**: run for this note with `target/release/stitchwort` built from
  `main` at `197d271c`, Node 22.23.3, Apple M4 Pro, on a shared machine.
  Times are single runs of the whole `stitchwort run`, including about
  0.2 s of checking.
- **[source]**: read in the code at that commit.
- **[inferred]**: my reasoning, not tested.

Claims about other languages link to a source that was opened for this note.

The scratch programs aren't committed. Their text is in this note wherever
it matters.

**Argument order.** Rule E (SW-450) is moving std to list-first, so this
note writes `List.map xs f` and `xs.map f`. On `main` today, std is still
callback-first, `List.map f xs`, so the scratch programs use that order.

## 0. Summary

**The problem.** `List.map collatzSteps xs` is refused (E-PARTIAL), and so
is a partial function that maps itself over its children (E-PARTIAL-CALLBACK).
The only route is a hand-written `mapP`, which is partial itself. It costs a
tick per element, and at a million elements it takes about 1.75x the time of
`List.map` natively and 1.3x with `--js` (§5.1).

**The proposal.** Add a second index beside the effect row: a *divergence*
index, `Total` or `MayDiverge`. A computation in a bare row `{e}` becomes
`CompD d e a`, which is `CompIn e a` (today's type) when `d` is `Total`, and
`Delay` (a partial computation) when `d` is `MayDiverge`.
- `{e}` keeps its spelling. It now means "whatever `e` is, including
  partial", much as `e` does in Koka.
- Only a row variable that a signature uses *bare* gets a divergence index.
  A row with abilities, `{A | e}`, stays total, because handlers can't run
  partial code (partial.md §7.3.8).
- So `List.map` takes partial callbacks with **no change to its source**.
  `xs.map collatzSteps` has type `{Partial} List Nat`, and
  `xs.map (x => x + 1)` is still plain `List Nat`.

**Why it's sound.** No kernel change and no new constant. `CompD` is an
ordinary definition by cases, like `CompIn`. A partial result is still a
`Delay`, which only the runner steps, so it can't hide (principle 1) and
checking never runs it (principle 2). The 80 std theorems about `List.map`
are about its total instance, which computes exactly as today (§3).

**Ticks.** Checked with an emulation of the new `map`: it adds no ticks.
`List.map collatzSteps [3, 7, 27]` takes 134 ticks, the same as the three
calls added up, against 137 with `mapP`. The self-mapping `countNodes 100`
takes 42 ticks, against 84 with `mapP` (§4) **[ran]**.

**Runtime.** The runners already step `Delay` values with their frames on
the heap. The emulation runs a million elements on both backends,
natively in 0.72 s against 0.57 s for the total `List.map` and 1.00 s for
`mapP` (§5) **[ran]**. Pure uses stay on today's loop by specialising at
`Total` as well as at the empty row.

**D1182, partial calls 3x slower.** A profile puts about half the native
time of a partial loop in allocating and freeing each call's request,
against almost none for the total loop **[ran]**. Two cheap runner fixes,
then a direct loop for tail self-calls. Each keeps the tick trace identical,
and each is gated on a benchmark (§5.4).

**The plan.** Five lanes: library and elaborator; backends; diagnostics and
examples; then the two D1182 lanes (§7.4). Other std functions (`filter`,
the folds, `any`/`all`) get partial callbacks when they become
effect-polymorphic, one at a time, each when a program needs it (§7.1).

## 1. Where things stand

Each scratch program starts with `import Std (List, Fail)`.

| # | Program | Result today **[ran]** |
|---|---|---|
| 1 | `List.map collatzSteps [3, 7, 27]` in a partial `main` | E-PARTIAL |
| 2 | `countNodes` mapping itself over its children | E-PARTIAL-CALLBACK |
| 3 | `List.filter isLong xs` with a partial `isLong` | E-TYPE-MISMATCH |
| 4 | A user's `twice (k: () -> {e} Nat)` given a partial `k` | E-PARTIAL, with misleading advice |
| 5 | `test "…" := List.map collatzSteps [3, 7, 27] == [7, 16, 111]` | E-PARTIAL |
| 6 | Two callbacks sharing `{e}`, one pure and one `Fail`, in both orders | works |
| 7 | A signature with only bare `{e}`, whose body handles `Fail` around the callback | works |
| 8 | Stage 3's `map`, emulated with a total function that builds a partial computation | works, no extra ticks |

**1. Mapping a partial function.**

```
def collatzSteps (n: Nat): {Partial} Nat :=
  if n <= 1 then 0 else 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def main(): {IO, Partial} () :=
  let steps := List.map collatzSteps [3, 7, 27]
  IO.print "${steps}"
```
```
[E-PARTIAL] Error: a partial function can't be used where a total one is expected
 7 │   let steps := List.map collatzSteps [3, 7, 27]
   │                         ──────┬─────
   │                               ╰─────── this might not finish: its type says `Partial`
   │ Note 1: a function whose type doesn't say `Partial` must finish; a row variable like `e` never stands for `Partial`, so a function taking `{… | e}` can't be given a partial one
   │ Note 2: to accept partial functions, write `Partial` in the row: `{Partial | e}`
```

**2. A partial function mapping itself** (G3′; the message was fixed in
SW-447):

```
def children (n: Nat): List Nat := if n < 3 then Nil else [n / 2, n / 3]

def countNodes (n: Nat): {Partial} Nat := 1 + List.sum (List.map countNodes (children n))
```
```
[E-PARTIAL-CALLBACK] Error: `countNodes` can't be passed to `List.map` here
 5 │ def countNodes (n: Nat): {Partial} Nat := 1 + List.sum (List.map countNodes (children n))
   │                         `countNodes` calls `countNodes`, so as a value it makes requests that only `countNodes`'s own definition can answer
   │ Note 1: `List.map` can't take a partial callback yet: the row variable in its signature stands for total rows only, so changing its signature won't help
   │ Note 2: instead, write a recursive helper marked `Partial`, like `mapP` in examples/accept/partial.sw, and pass `countNodes` to that
```

**3. `filter`.** `List.filter` takes a pure callback today, so it's a plain
mismatch: `expected Nat -> Bool, but this has type Nat -> {Partial} Bool`.

**4. A user's row-polymorphic helper.**

```
def twice (k: () -> {e} Nat): {e} Nat := k () + k ()

def main(): {IO, Partial} () := IO.print "${twice (() => collatzSteps 27)}"
```
```
[E-PARTIAL] Error: a computation that might not finish can't run here
 8 │ def main(): {IO, Partial} () := IO.print "${twice (() => collatzSteps 27)}"
   │                                                          ╰───────── `collatzSteps` is `Partial`: it might not finish
   │ Note: code whose type doesn't say `Partial` must finish, so it can't run anything that might not; add `Partial` to the enclosing function's type (`-> {Partial} …`)
```

The note is wrong here: `main` already says `Partial`. The real reason is
that `twice`'s `e` can't be partial. After stage 3 this program checks.

**5. A test** (tests may call partial code since D1183): the same E-PARTIAL
as program 1, with the same notes.

**6 and 7: what stage 3 must keep.** These pass today, and are the cases
the design has to be careful with (§2.3, §2.4):

```
def both (f: Nat -> {e} Nat) (g: Nat -> {e} Nat) (n: Nat): {e} Nat := f n + g n
def check (n: Nat): {Fail} Nat := if n > 10 then Fail.fail "big" else n
def pureFirst (n: Nat): {Fail} Nat := both (x => x + 1) check n
def failFirst (n: Nat): {Fail} Nat := both check (x => x + 1) n
```
```
-- Uses `e` only bare, but the body handles `Fail` around `f`, so `e` must be total.
def tryEach (xs: List Nat) (f: Nat -> {e} Nat): {e} List (Result Nat Text) :=
  List.map (x => Fail.toResult (() => if x > 10 then Fail.fail "big" else f x)) xs

test "tryEach" := tryEach [1, 20] (x => x * 2) == [Ok 2, Err "big"]
```

Both tests pass.

**8. Stage 3's `map`, emulated.** On today's build a self-recursive function
whose result is a `Delay` is always translated into a partial definition,
with a tick per call (partial.md §7.3.2). But a function that *returns a
function* returning a `Delay` counts as total (partial.md §9.4,
"Classification"). So this builds a partial computation by structural
recursion, which is exactly what the new `map` does at a partial row:

```
def mapK (f: a -> {Partial | e} b) (list: List a): () -> {Partial | e} (List b) :=
  match list with
    | Nil => () => Nil
    | Cons x xs => () => Cons (f x) (mapK f xs ())
```

`mapK collatzSteps [3, 7, 27] ()` prints `[7, 16, 111]`. Its ticks and
speed are in §4 and §5.

## 2. The design: a divergence index beside the row

### 2.1 Library definitions

These go in `core/Effect.sw`, next to `CompIn`. Like `Effects`, they're
library-internal (D1122): programs can't name the constructors or take a
`Divergence` apart.

```
-- Whether a computation in a bare row `{e}` may not finish.
type Effect.Divergence: Type =
  | Total
  | MayDiverge

-- `{e} a` once `e` may be partial. When total, it's today's type.
def Effect.CompD: Divergence -> Effects -> Type -> Type
  | Total, row, a => CompIn row a
  | MayDiverge, row, a => Delay (rowOp row) (rowRes row) a

def Effect.doneD [a: Type]: (d: Divergence) -> (row: Effects) -> a -> CompD d row a
  | Total, row, value => doneIn row value
  | MayDiverge, row, value => now value

def Effect.bindDv [a b: Type]: (d: Divergence) -> (row: Effects) ->
    CompD d row a -> (a -> CompD d row b) -> CompD d row b
  | Total, row, c, next => bindIn row c next
  | MayDiverge, row, c, next => bindD c next

-- A total computation in `{e}`, moved to where `e` may be partial.
def Effect.liftD [a: Type]: (d: Divergence) -> (row: Effects) -> CompIn row a -> CompD d row a
  | Total, row, c => c
  | MayDiverge, row, c => lift (liftIn row c)

-- A computation in `{e}`, moved into the partial row `{Partial | e}`.
def Effect.delayD [a: Type]: (d: Divergence) -> (row: Effects) ->
    CompD d row a -> Delay (rowOp row) (rowRes row) a
  | Total, row, c => lift (liftIn row c)
  | MayDiverge, row, c => c
```

Two facts make this fit what exists.
- **`{Partial | e} a` is already `Delay (rowOp e) (rowRes e) a`**
  (`effects.rs`, `comp_type`) **[source]**. So `CompD MayDiverge e a` *is*
  `{Partial | e} a`, by computation. A `mapP`-style function and the new
  `map` agree on what a partial computation in `{e}` is.
- **`CompD Total e a` is `CompIn e a`**, and `CompIn Empty a` is `a`. So a
  pure use of `map` computes exactly as it does today.

This is partial.md §10.7's "a type-level `Bool` selecting `Comp` or `Delay`,
with `bind`/`lift` defined by cases". It's also the "separate total / may not
finish marker" that partial-stage-2.md §4 asked for.

### 2.2 What `{e}` means in a signature

**The rule (D1214).** In a definition's type, a row variable `e` gets a
divergence index `d` (an implicit parameter, like `e` itself) when **every
occurrence of `e` in the type is a bare row `{e}`**. Each `{e} a` then means
`CompD d e a`. Otherwise `e` has no index, and `{e} a` is `CompIn e a` as
today.

| Signature | `e` may be partial? | Why |
|---|---|---|
| `List.map (xs: List a) (f: a -> {e} b): {e} List b` | yes | only bare `{e}` |
| `twice (k: () -> {e} Nat): {e} Nat` | yes | only bare |
| `Fail.toResult (prog: () -> {Fail | e} a): {e} Result a Text` | no | `{Fail | e}` |
| `IO.simulate (input: List Text) (prog: () -> {IO | e} a): {e} …` | no | `{IO | e}` |
| `Checker.run (c: Checker e) (xs: List Nat): {e} (List Nat)` | no | `e` is a data type's argument |

So in std today only `List.map` gains partial callbacks. A grep finds 19
definitions with bare-only rows across std, examples, docs and the guide,
such as `twice`, `applyTwice` and `mapTwice` **[ran]**. All of them gain
partial callbacks too, with no source change.

**Why only bare rows.** A computation in `{A | e}` is a `Comp`, a tree that
handlers fold over. Letting `e` be partial there would make the whole row a
`Delay`, and a handler can't fold a `Delay` (partial.md §7.3.8). A function
that extends `e` without handling it, such as a hypothetical `forEachPrint
(f: a -> {IO | e} b): {IO | e} ()`, could in principle be partial. But that
needs a divergence index on every row with a tail, and `translate`/`mapSig`
variants for each. No program needs it yet, so it stays out (D1214).

**A body that needs `e` total (D1215).** Program 7's `tryEach` uses `e`
only bare, so the rule gives it an index. But its body moves `f x` into
`{Fail | e}` to handle it, which is impossible if `e` may be partial. The
recommendation is that the elaborator then **checks the definition again
with `e` total**, exactly as today. This is the same "try the general form,
then the narrower one" that tests (D1183) and `main` (stage 2) already use.
- Nothing that checks today stops checking.
- No new syntax.
- The cost: two definitions with the same written signature can differ in
  whether they take partial callbacks. Hover shows it ("`e` is total: the
  body handles it at line 7"), and a caller who passes a partial callback
  gets that sentence in the error.

The alternative is to make it an error and add syntax to say "`e` is total".
Every option for that syntax is a new word in rows, and no program needs it.

### 2.3 Elaboration

In `crates/elab/src/effects.rs`, a `Row`'s `partial: bool` becomes three
cases: total, partial, or "partial if `d`" (a variable or an unknown).
Everything that today builds `CompIn`/`doneIn`/`bindIn`/`liftIn` for a bare
row builds the `…D` forms when the row has an index **[source]** for where
(`comp_type`, `lift`, sequencing at `effects.rs:809`).

| Moving a computation | from | to | How |
|---|---|---|---|
| a total value or call | total | `{e}` with `d` | `liftD d e` (at `Total` it's the computation itself) |
| | `{e}` with `d` | the same row | unchanged |
| | `{e}` with `d` | a partial row | `delayD d e` |
| | `{e}` with a rigid `d` | a total row, or a handler | refused (E-PARTIAL), or the fallback of §2.2 |

**Inference.** At a call of `List.map`, `d` is an unknown `?d`, as `e` is
`?e` today. The rules follow the row rules of effect-polymorphism.md §5.C.1:
- A `Delay op res B` (a partial callback or result) solves `?d := MayDiverge`
  and `?e` from `op` as today's rule does for a `Comp`.
- A `Comp op res B` solves `?d := Total`.
- A total value against `CompD ?d ?e B` doesn't solve `?d`. It's wrapped in
  `liftD ?d ?e`, which computes once `?d` is known. So, in program 6's shape,
  one partial callback and one total callback give `MayDiverge` in either
  order.
- When nothing settles `?d`, it defaults to `Total`, at the same time as
  `?e` defaults to `Empty`. `check::pure_first` (plain calls first in a pure
  context) treats an unknown `?d` as `Total`.

Program 6 shows today's row inference already does this for one pure and
one `Fail` callback, in both orders **[ran]**. That `?d` behaves the same
way is **[inferred]**, and the build's tests must show it.

**Messages** print `CompD d e a` as `{e} a`, `CompD MayDiverge e a` as
`{Partial | e} a`, and `CompD Total e a` as `CompIn e a` is printed today.
Users never see `Divergence`.

### 2.4 Inside a partial definition: `countNodes`

While a partial group is described, a recursive reference has the type
`X -> Delay (Plus (Rec A) op) … Y`, and `Rec A` is a row label
(partial.md §7.3.4, §9.4) **[source]** (`effects::REC`). Passing
`countNodes` to `List.map` solves `?d := MayDiverge` and `?e := Ops (Plus
(Rec A) NoOp) …`. The map's result is then a `Delay` in the description's
own row, which `List.sum` consumes inside the description through
`bindD`. That's exactly the case §7.3.4 calls fine: "a place whose type is
polymorphic in the rest of the row".

- The **escape checks** don't change. Returning the mapped computation out
  of the definition is still E-PARTIAL-ESCAPE, because its type has the
  private row in it.
- **E-PARTIAL-CALLBACK still exists**, for helpers whose callback has a
  *fixed* row, such as `useP (k: Nat -> {Partial} Nat)`
  (`reject/partial-callback.sw`). Only std's `map` stops triggering it
  (§7.2).

### 2.5 What doesn't change

- The kernel. No new primitive, and no computation rule for `Delay`.
- Handlers. A handled computation still can't be partial. `Fail.toResult`
  around `xs.map collatzSteps` is still E-PARTIAL.
- Rows with abilities, data types with row parameters (D1160), and
  `IO.simulate` (`reject/partial-row-variable.sw`) stay total.
- How partial definitions are recognised. A definition is partial when its
  type ends in `Delay` (`partial.rs`, `partial_after`, which looks at the
  forced result type) **[source]**. `List.map`'s result type is `CompD d e
  (List b)` with `d` a variable, which is stuck, not a `Delay`. So `map`
  stays an ordinary structurally recursive function, checked by the
  termination checker as today.

### 2.6 Alternatives considered

- **A third `Effects` constructor**, with `CompIn (Diverging op res) a =
  Delay op res a`. Rejected, as partial-stage-2.md §4 says.
  - `{A | e}` is `Comp (Plus A (rowOp e))`, which would quietly give a total
    type to a row that says it may diverge.
  - Any law proved for every row by cases on `e` would get a case it can't
    prove, because `bindD` has no computation rules.

  With a separate index, `Effects` and every law about it are unchanged
  (§3.3).
- **A separate `mapP` in std** (as F\* has separate `map`s per effect, §6).
  This goes against D1110's one `map`, and keeps the tick per element.
- **Hide partiality from types** (Idris, Lean, §6). This goes against
  principle 1.
- **An explicit marker on the polymorphic side**, such as `{e?}`. That's
  noise on every row-polymorphic signature, for something the bare-row rule
  infers.

## 3. Soundness

### 3.1 Principle 1: no hidden divergence

A partial callback makes the call's type `CompD MayDiverge e T`, which
computes to `Delay … T`, which messages print as `{Partial | e} T`. From
there everything is stage 1: total code can't run it (E-PARTIAL), and the
caller must itself say `Partial`. A function whose signature has `{e}` can
only become partial when its *caller* passes a partial callback, and then
it's the caller's type that says so.

Could code that is polymorphic in `d` get a value out of a `MayDiverge`
computation? It would need to take `d` apart, which only the library can
(D1122). Even then, the `MayDiverge` branch holds a `Delay`, and nothing
eliminates a `Delay`.

### 3.2 Principle 2: checking never runs effects; consistency

- **No new constants.** Partial.md §7.8's argument (interpret every `Delay
  op res a` as a one-element set) is untouched. `Divergence`, `CompD` and
  the `…D` functions are ordinary definitions that the kernel re-checks.
  `CompD` is a large elimination into `Type`, as `CompIn` and
  `Effect.sigOp` already are.
- **Conversion may now unfold `map` at a partial row.** For example, a type
  mentioning `List.map [3] collatzSteps` reduces through `bindDv MayDiverge`
  to `bindD (collatzSteps 3) …`, and stops: `collatzSteps 3` is `pfix …`,
  which is neutral. Building a `Delay` runs nothing (partial.md §7.4.1). It's
  what happens today when a type mentions `collatzSteps 3`.
- **Tests** run partial code only in `stitchwort test` and the playground's
  Tests tab, never while checking (D1183). A test that maps a partial
  function is just a partial test.

### 3.3 Proofs about `List.map`

- **Total instances are unchanged.** In a theorem such as `mapCong`, `f` is
  pure, so `?d` defaults to `Total` and `?e` to `Empty`. `map`'s body then
  computes through `bindDv Total Empty c k` to `bindIn Empty c k` to `k c`,
  which is today's computation with one more step. This is the argument
  effect-polymorphism.md stage 3 used when `mapIn` was folded into `map`,
  where all 80 theorems mentioning `List.map` checked unchanged **[source]**
  ("As built (stage 3)"). For stage 3 here it's **[inferred]**. The build's
  gate is that all 80 check with no edits.
- **Effectful instances** (`Fail.toResultMap`, whose `f: a -> {Fail} b`)
  solve `?d := Total` from the `Comp` type, so they're unchanged.
- **Partial instances have nothing to prove**, as in stage 1 (partial.md
  §7.7). `rfl: List.map [3] collatzSteps = …` fails like
  `soundness/partial-unfold.sw`.
- **Row laws.** No std theorem quantifies over `Effects`: outside
  `core/Effect.sw` no std file mentions it **[ran]** (grep). The laws in
  `Effect/Laws.sw` are about `Comp` trees, which this doesn't touch. A
  future law "for every row" is stated over `Effects`, or over `CompD Total
  e`, which computes to `CompIn e`. Either way it keeps its proof by cases
  on `e`. A law over every `d` would have an unprovable `MayDiverge` case.
  That's the point of the separate index: partiality is never a case of a
  row.

### 3.4 What the argument doesn't cover

As in partial.md §7.8, it says nothing about whether the runners run the
right program. That's tested: the same traces (operations, replies, ticks)
on the reference evaluator, natively and in JS (§7.3).

## 4. Ticks: "it adds no ticks: only the callback's recursion counts"

**The rule** (partial.md §7.4.3): a tick is a recursive call, meaning a
recursion request answered by a `pfix`'s `Tie`. Entering a partial function
is free, and so is building or sequencing a `Delay`. The new `map` isn't a
partial definition (§2.5): it's total code that builds `bindD`/`now`
values. So it makes no requests, and only `f`'s own recursion ticks
**[inferred]** from the rule.

**Checked** **[ran]** with a scratch Rust test on the reference runner
(`Session::run_main_with`, counting `Event::Tick`), not committed. It uses
the `mapK` emulation of §1 and `mapP`. `inc` is a `{Partial}` function that
doesn't recurse.

| Program | Ticks | Printed |
|---|---|---|
| `collatzSteps 3 + collatzSteps 7 + collatzSteps 27` | 134 | `134` |
| `mapP collatzSteps [3, 7, 27]` | 137 | `[7, 16, 111]` |
| `mapK collatzSteps [3, 7, 27] ()` (stage 3's shape) | **134** | `[7, 16, 111]` |
| `mapP inc [1, 2, 3, 4, 5]` | 5 | `[2, 3, 4, 5, 6]` |
| `mapK inc [1, 2, 3, 4, 5] ()` | **0** | `[2, 3, 4, 5, 6]` |
| `countNodes 100` through `mapP` | 84 | `43` |
| `countNodes 100` through `mapK` (polymorphic in `e`) | **42** | `43` |

43 nodes are 42 recursive calls, which is exactly the emulation's count.
`mapP` adds one per element: 3 for three elements, and one per child (42)
for `countNodes`. A third emulation, by `List.foldRight` with a partial
accumulator, also gives 134 and 0.

**One consequence.** The runner's per-step work budget restarts at every
tick and every operation (partial.md §9.4). A map with a callback that never
recurses is one long step, as a total map is. Its budget is the one any
total code has, so this isn't a new limit **[inferred]**.

## 5. Runtime

### 5.1 How the runners run it

At a partial row, generic `map` builds, per element,
`bindD (f x) (y => bindD (map xs f) (ys => now (Cons y ys)))`. The recursive
`map xs f` is inside a continuation, so it's built only when the runner
reaches it. All three runners already step `Delay` values with heap frames:
- natively, `crates/rt/src/run.rs`, with `Bind`/`Map`/`Tie`/`Await` frames;
- in JS, `crates/js/src/run.rs`, a copy of the same machine;
- on the reference evaluator, `crates/core/src/step.rs`

**[source]**. So nothing new runs, and each element costs a `Bind` frame
while its tail is mapped. That's the same shape as `mapK` **[inferred]**.

**Measured** **[ran]** (`p1-perf.sw`: sum of the mapped `List.range n`; RSS
is the peak):

| Program | Native, 100k | Native, 1M | `--js`, 100k | `--js`, 1M |
|---|---|---|---|---|
| `List.map (x => x + 1)` (total) | 0.18 s | 0.57 s, 578 MB | 0.32 s | 0.64 s, 438 MB |
| `mapP inc` (today's workaround) | 0.21 s | 1.00 s, 673 MB | 0.29 s | 0.82 s, 728 MB |
| `mapK inc` (stage 3's shape) | 0.18 s | **0.72 s**, 638 MB | 0.30 s | **0.57 s**, 468 MB |
| `mapP collatzSteps` | 4.85 s | – | 1.69 s | – |
| `mapK collatzSteps` | 4.86 s | – | 1.66 s | – |

- **Stack-safe** at a million elements on both backends.
- At 3,000,000 elements natively, all three, including the total `map`,
  stop with E-RESOURCE ("recursed more deeply than allowed"), while `--js`
  runs all three. So the native frame limit is hit somewhere other than the
  map (not investigated), and the emulation shows no map-specific limit
  **[ran]**.
- With Collatz callbacks, the callback's 10.75 million ticks dominate, so
  `map` vs `mapP` doesn't matter there. D1182 does (§5.4).

The real generic `map` will differ from `mapK`: a `bindDv` case on `d`, and
two `bindD`s per element where `mapK` has a closure call. Within about 1.5x
of the total `map` is **[inferred]**, and it's the build's acceptance
figure (§7.3).

### 5.2 Fusion and specialisation (design E)

Pure uses of `map` run as a loop because the backends specialise
row-polymorphic code at `Empty` (`crates/rt/src/specialise.rs`, shared with
JS) **[source]**. If `map` gains a `d` parameter and nothing else changes,
the pure variant would still test `d` on every element through `bindDv`.
That breaks stage 2's "pure `map` within 10%".

So `Divergence` joins `Effects` in design E's list of types that drive
specialisation, with `Total` as the constructor specialised on (D1216). The
variant for `[Empty] [Total]` is today's variant: `bindDv Total Empty c k`
inlines to `bindIn Empty c k` and then to `k c`, and TRMC makes the loop. At
`MayDiverge`, generic code runs. Design E says a list entry is "a design
decision, not a tuning knob", hence a decision.

The other runtime optimisations aren't affected [inferred]:
- the state-handler fusion (4d) and closed signature maps (4f) are about
  handlers and `Comp`, which never meet `MayDiverge`;
- lazy resumption (D1162 §9.2) chooses by the fold's carrier, and a
  carrier is never `CompD MayDiverge` because handlers can't be partial.

### 5.3 `build --js` (exports)

Exports still can't mention `Delay` (E-JS-PARTIAL). Inside an export, a
partial use of `map` is erased as stage 1 erases any partial computation.
`build --js` turns each call of `now`, `bindD` and `lift` into the token
`delayed` without computing its arguments (`crates/js/src/lib.rs`,
`def_call`) **[source]**. So generic `map` at `MayDiverge` builds tokens,
which is correct while no total code can tell two `Delay`s apart
(partial.md §7.6).

### 5.4 D1182: making partial calls cheaper

**The cost, measured** **[ran]** (`p2-collatz.sw`: summing the Collatz step
counts for 1..100,000, which is 10,753,840 steps):

| Version | Native | `--js` |
|---|---|---|
| Total, with fuel | 1.03 s | 0.50 s |
| Partial, tail-recursive | 3.25 s | 0.99 s |
| Partial, `1 + steps (…)` (non-tail) | 4.77 s | 1.53 s |

Without the 0.2 s of checking, that's about 77, 284 and 425 ns per step
natively, and 28, 74 and 124 ns in JS: the "3x / 2x" of D1182.

**Where it goes.** A 3-second `sample` of the native tail loop **[ran]**:
- about 51% of the samples are in allocating, freeing and dropping values
  (mimalloc, `drop_glue`, `Rc` slices, `Vec` growth);
- 23% are in the machine's `run`;
- 8% are in the runner's `drive` and `push`;
- 7% are in arithmetic.

The total fuelled loop's profile has no allocator entries among the
functions sampled at least 5 times. Per recursive call, the native path
**[source]** (`crates/rt/src/run.rs`):
1. The description returns `lift (Call (L (Recur (pack args))) Done)`. That
   allocates the packed arguments, `Recur`, `L`, `Call` and `lift`.
2. `route` walks the marks to the `Tie`, `split_off`s the frames above it
   into a new `Vec` (even for a tail call, where it's only the `Tie`),
   and pushes an `Await` unless it's a tail call.
3. `Enter` pushes the `Tie` again and calls the description through
   `Machine::call`, which unpacks the request (`f.body`'s case).

The options below are ordered by cost. In each, the obligation is the
same, and it's all of it: **the trace stays identical**, meaning every
operation, reply and tick in order. The runner is outside the logic
(partial.md §7.9: a bug can make a program misbehave, never make the logic
unsound). So these are tested against the reference runner and the model
(`crates/partial-model`), and by the generated differential tests (4e).

| Option | What | Expected gain | Risk |
|---|---|---|---|
| **A. Runner fast paths** | For a tail request, leave the `Tie` in place: no `split_off`, no re-push. Reuse the request's buffers. | small, perhaps 10–20% **[inferred]** | low |
| **B. A request node** | The backends compile `g.recur args` to one runtime node, `Request(member, args)`, that the runner recognises directly, instead of five allocations. Only the backends change; the elaborated term doesn't, so no hash moves. | perhaps 1.5x **[inferred]**, from the allocation share | low: the node means exactly `lift (Call (L (Recur …)) Done)` |
| **C. Tail self-loop** | For a member whose row is just `{Partial}` (nothing to route), a tail request to itself or a sibling becomes a jump in a loop inside the step. The loop counts a tick, restarts the step budget and checks the tick limit at each turn, all without leaving the machine. Non-tail calls and calls to other partial functions take the normal path. | towards the fuelled loop **[inferred]** | medium: the tick must be counted exactly where the request would have been; the 4e generator gets loop shapes |
| D. Direct non-tail calls | Call the description directly, natively on heap frames, and in JS with a depth counter that falls back to a request past a bound. | most | high: operations inside the callee need the general path; JS stack; not now |

On C: the tick limit only exists for `Session::simulate` in Rust tests
(tests have none since D1183), and the playground's Stop terminates its
worker. So a loop that counts ticks itself needs no cooperation from the
runner beyond the counter **[source]** (partial-tests.md; `Policy::default()`
has `max_ticks: None`).

Recommended (D1219): A and B in one lane, then C, each kept only with a
benchmark showing at least 1.5x (the 4f rule), on both backends. D only
when a program needs it.

Stage 3 doesn't depend on D1182. `map` adds no ticks, so its speed doesn't
depend on the cost per tick. D1182 is about the callback's own recursion.

## 6. Prior art

**Koka.** Divergence is an effect label, `div`, in the same row as every
other effect.
- `total` is the empty row ("The _total_ effect represents the absence of
  any effect") and `div` is "The divergence effect: a divergent function
  may not terminate" ([`std/core/types.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core/types.kk)).
- `pure` is `<exn,div>` ([`std/core.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk)).
- `map` is `fun map(xs : list<a>, ^f : a -> e b) : e list<b>`
  ([`std/core/list.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core/list.kk)).
  The book says "this function has no other effect by itself since it does
  not diverge" ([Koka book §3.2.3](https://koka-lang.github.io/koka/doc/book.html)).
  So `e` may contain `div`, and `map` diverges exactly when `f` does. That's
  the behaviour proposed here.
- `while` has the type `(pred : () -> <div|e> bool, …) -> <div|e> ()`, and
  "both the effects of predicate and action are extended automatically until
  they match" (same book section).
- `div` is inferred when the checker can't prove termination: "if the
  termination checker finds that each recursive call decreases the size of
  an inductive data type … then we do not assign the divergent effect"
  ([Leijen, MSFP 2014, §2.7](https://arxiv.org/abs/1406.2061)).
- **The difference from here.** In Koka, `div` is a label like any other, so
  `e` can be partial even under `<exn|e>`. Here, partiality can't sit under
  a handler (partial.md §7.3.8), so only bare rows may be partial. Whether
  Koka lets a handler handle `div` isn't stated anywhere I found. Its kind is
  `X`, while handled effects have kind `HX` ([book §4.4.14](https://koka-lang.github.io/koka/doc/book.html)),
  which suggests not **[unverified]**.

**F\*.** `Dv` is "a primitive effect"; "a total computation `Tot t` can be
silently promoted to `Dv t`", and "it should be impossible to turn a `e:Dv t`
into a term of type `Tot t`". Also: "One cannot even state properties of `Dv`
computations in specifications"
([F\* book, Divergence](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).
The library has a separate `map` per effect:
- `val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)`
  ([`FStar.List.Tot.Base.fst`](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.List.Tot.Base.fst));
- `val map: ('a -> ML 'b) -> list 'a -> ML (list 'b)`, which "Hides
  [List.Tot.map] which requires … [f] to be a pure total function"
  ([`FStar.List.fst`](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.List.fst)).

So F\*'s subsumption (`Tot` into `Dv`) matches `liftD`. Its library is
design A of effect-polymorphism.md (separate functions), which D1110
rejected.

**Idris 2.** A total function must "Not call any non-total functions"
([Idris 2, Theorem proving](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)).
The checker looks at every global name a definition refers to
([`Termination/References.idr`](https://github.com/idris-lang/Idris2/blob/main/src/Core/Termination/References.idr):
"Check that the names a function refers to are terminating").
- So `total foo = map partialF xs` would be refused for naming `partialF`,
  while `map` itself, whose `f` is a parameter, stays total **[inferred from
  the source, not compiled]**.
- Partiality isn't in types, so there's nothing to be polymorphic in. That
  goes against principle 1.

**Lean 4 `partial`.** "Functions marked partial are treated as opaque
constants by the kernel and are neither unfolded nor reduced. All that is
required for soundness is that their return type is inhabited." And:
"Partial functions may still be used in compiled code as usual, and they may
appear in propositions and proofs; their equational theory in Lean's logic
is simply very weak"
([Lean reference, Recursive definitions §7.6.6](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)).
- So `List.map partialF xs` is an ordinary call, and the type doesn't say it
  may not finish **[inferred]**.
- `partial_fixpoint` is for "Functions that return values in a suitable
  monad, such as the Option monad" (same page).

**Agda and Coq: Delay as a monad.**
- Agda's `Delay` has `bind : Delay A i → (A → Delay B i) → Delay B i`
  ([`Codata/Sized/Delay.agda`](https://github.com/agda/agda-stdlib/blob/master/src/Codata/Sized/Delay.agda))
  and a monad instance (`Codata/Sized/Delay/Effectful.agda`).
- Lists have a generic `mapA : … → (A → F B) → List A → F (List B)`, named
  `mapM` for monads
  ([`Data/List/Effectful.agda`](https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Effectful.agda)).
- Coq's Interaction Trees provide `Monad_itree` and `iter`
  ([`ITreeDefinition.v`](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Core/ITreeDefinition.v)),
  and ExtLib's `mapT` traverses a list in any applicative
  ([`Data/List.v`](https://github.com/coq-community/coq-ext-lib/blob/master/theories/Data/List.v)).

So in both, a partial callback goes through the monadic traversal, and the
plain `map` doesn't take one. Stitchwort's one `map` is that traversal when
`d` is `MayDiverge`, and the plain map when the row is empty, because
`CompD` computes. (Capretta's original: "To every type A we associate a type
of partial elements Partial(A)",
[LMCS 2005](https://arxiv.org/abs/cs/0505037).)

## 7. Migration

### 7.1 Which std functions get partial callbacks

A function gets partial callbacks once it's effect-polymorphic in a bare row
(§2.2), and not before. Today that's only `List.map` **[source]**
(`List/Toolkit.sw`: `filter`, `foldLeft`, `any`, `all`, `find` and
`filterMap` take pure callbacks).

| Function | Today | To take partial callbacks | Notes |
|---|---|---|---|
| `List.map` | `{e}` | automatic in stage 3 | |
| `List.filter` | pure | becomes effect-polymorphic (D1120) | evaluation order to fix: today `filterStep x (filter p xs) (p x)` passes the rest first; the effectful one should call `p x` first |
| `List.foldLeft` | pure | same | tail-recursive: at a partial row it builds one `bindD` per element, which the runner pops as it goes |
| `List.foldRight` | pure, via `foldLeft` | follows `foldLeft` | |
| `List.any` / `List.all` | pure | same | whether they stop calling `p` after the first decisive result is a semantic choice for that lane |
| `List.find`, `filterMap`, `flatMap` | pure | same | `flatMap` is `concat (map …)`, so it follows `map` once its own signature is `{e}` |

Recommended (D1217): stage 3 is `map` only. Each of the others becomes
effect-polymorphic, and so also partial-capable, in its own lane when a real
program needs it (D1120, and the backlog rule). G3″ (`filter` with a partial
predicate) came from a scratch program, not a real one.

### 7.2 Diagnostics

- **E-PARTIAL-CALLBACK** stays for fixed-row helpers (`useP`), unchanged.
  Its std-specific note ("`List.map` can't take a partial callback yet…
  write `mapP`") goes. When the helper is a std function with a *pure*
  callback (`List.filter`), the note says "`List.filter`'s callback can't be
  partial or perform abilities; so far only `List.map`'s can".
- **E-TYPE-MISMATCH** for a partial function given to a pure-callback std
  function (program 3) gets the same note.
- **E-PARTIAL notes.** "a row variable like `e` never stands for `Partial`"
  becomes accurate again:
  - for a row with abilities: "`{… | e}` must be total: handlers can't run
    partial code";
  - for the fallback of §2.2: "`tryEach` needs a total callback: its body
    handles `Fail` around it at line 7";
  - program 4's "add `Partial` to the enclosing function's type" is said
    only when the enclosing type lacks `Partial`.
- **No new codes** (D1218).

### 7.3 Examples and tests that would show it works

- **`examples/accept/partial-map.sw`**:
  - `xs.map collatzSteps` and `List.map xs collatzSteps` in a partial
    `main`;
  - `countNodes` mapping itself;
  - a callback that is both partial and prints (`{IO, Partial}`, so `e` is
    `IO` and `d` is `MayDiverge`);
  - `twice` and `both` (program 6) with one partial callback and one total,
    in both orders;
  - a total callback in partial code (unchanged);
  - tests per D1183, e.g. `test "…" := [3, 7, 27].map collatzSteps == [7, 16, 111]`.
- **Still refused:**
  - a total function that maps a partial callback (E-PARTIAL);
  - `Fail.toResult (() => xs.map collatzSteps)` (E-PARTIAL);
  - program 7's `tryEach` given a partial callback (E-PARTIAL, with the
    fallback note);
  - returning the mapped computation out of `countNodes`
    (E-PARTIAL-ESCAPE);
  - a program naming `Divergence` or `MayDiverge` (the D1122 check, as
    `reject/row-internal-inspect.sw`);
  - `rfl` across a partial `map` (E-REFL, as `soundness/partial-unfold.sw`).
- **Unchanged:** the 80 std theorems about `List.map` (the gate of §3.3);
  program 7 checks and passes; `reject/partial-callback.sw` and
  `partial-row-variable.sw`.
- **`reject/partial-callback-std.sw`** becomes an accept example (it's
  `countNodes`).
- **Ticks** (`crates/driver/tests/partial.rs`): `List.map collatzSteps [3, 7, 27]`
  134, `List.map inc [1..5]` 0, `countNodes 100` 42, on all three runners,
  with traces identical.
- **Speed:**
  - pure `map` at 1M within 10% of before (stage 2's rule), checked with the
    bench baseline;
  - a partial `map` with `inc` at 1M within 1.5x of the total `map`, natively
    and with `--js`.
- **Playground:** a partial `map` at 1M in `crates/web`'s tests.
- **Docs:** guide chapter 7 (partial) shows `xs.map collatzSteps`; chapter
  18 (effect polymorphism) says `{e}` may be partial; `syntax.md`;
  `examples/accept/partial.sw` keeps `mapP` as an example of a written
  `{Partial | e}` helper; the stage-2 note's G3 points here.

### 7.4 Build plan

Each lane starts from local `main`, after rule E (SW-450) lands, since it
rewrites `List.map`'s argument order.

| Lane | Work | Model tier | Checks |
|---|---|---|---|
| **3a. Library and elaborator** | §2.1's definitions, library-internal; `Row`'s three-way partiality; the signature rule; sequencing and moves (§2.3); `?d` inference, postponement and defaulting, `pure_first`; the fallback of §2.2; message printing. **Plus** design E's list gains `Divergence` (§5.2), because without it pure `map` slows down, so the two must land together. | Opus or Sonnet (judgement in the core) | the 80 theorems with no edits; programs 1, 2, 4, 5 check; 6 and 7 still pass; the reject list of §7.3; the pure `map` bench within 10% |
| **3b. Runners** | Partial `map` on native, `--js` and the reference runner; tick and trace agreement tests; the 1M speed figures; the playground test; the 4e generator gets partial callbacks through `map`. | Sonnet | `partial.rs` tick tests, `run_js`/`run_reference` on the new example, `effect_runtime` |
| **3c. Diagnostics, examples, docs** | §7.2 and §7.3's examples and docs; retire the std note of E-PARTIAL-CALLBACK. | DeepSeek, from an exact list | the named examples' snapshots |
| **3d. D1182 A+B** | runner fast paths and the request node, both backends | Sonnet | the model comparison in `partial.rs`; `p2-collatz` before and after (≥1.5x, or drop it) |
| **3e. D1182 C** | the tail self-loop | Sonnet | the same, plus 4e loop shapes |

3a is the largest. It's mostly `effects.rs`, which builds computation types
in many places, as effect-polymorphism.md design C warned. If it turns out
too large, the fallback of §2.2 can split off as its own lane, after 3a with
the plain rule. In the meantime program 7 would be a known regression on a
branch, never merged.

## 8. What I couldn't verify

- That `?d` infers in every order as rows do (§2.3). Program 6 shows it for
  rows only.
- The real generic `map`'s speed at a partial row. `mapK` is an emulation
  with closures instead of `bindDv` (§5.1).
- The D1182 gains in §5.4. Only the cost and its profile were measured.
- Whether Koka's `div` can be handled (§6).
- Idris's behaviour on `map partialF`, which I read in its source but didn't
  compile.
- Why the native run stops at 3,000,000 elements for the total `map` too
  (§5.1). It's not specific to this design.

## 9. Decisions for Matt

1. **D1213. How partiality reaches `{e}`.**
   - (a) **Recommended:** a separate divergence index (`Total` /
     `MayDiverge`) beside the row, with `CompD d e a` (§2.1). Koka's
     behaviour, restricted to what handlers allow.
   - (b) A third `Effects` constructor. Wrong, for §2.6's two reasons.
   - (c) Keep `mapP`-style helpers in std.

   Reason: (a) is the only one that changes neither the kernel nor any law
   about rows, and it gives one `map`.

2. **D1214. Which row variables may be partial.**
   - (a) **Recommended:** those a signature uses only bare (`{e}`). Rows with
     abilities (`{A | e}`) and data types' row parameters stay total.
   - (b) Every row variable, with a divergence index on rows with abilities
     too. More general, but needs `translate`/`mapSig` variants throughout,
     and no program needs it.
   - (c) Only where written, with a marker such as `{e?}`.

   Reason: (a) gives `map` and every map-like helper partial callbacks with
   no source change.

3. **D1215. A body that needs its bare `e` total** (program 7).
   - (a) **Recommended:** check it again with `e` total, silently, and say
     so in hover and in callers' errors. Nothing that checks today breaks,
     and there's no new syntax.
   - (b) An error, plus new syntax to say "`e` is total".
   - (c) An error with no way to say it, which would break program 7.

4. **D1216. Specialise at `Total`.** Add `Divergence` to design E's list of
   types that drive specialisation, specialising at `Total`, so pure `map`
   stays today's loop.
   - **Recommended:** yes.
   - The alternative, no specialisation, costs a test per element on every
     pure use.

5. **D1217. Which std functions in stage 3.**
   - (a) **Recommended:** `List.map` only (automatic). `filter`, the folds,
     `any`/`all`, `find` and `filterMap` gain partial callbacks when each
     becomes effect-polymorphic, one at a time, on a real program's need
     (D1120).
   - (b) Make `filter`, `foldLeft`, `any` and `all` effect-polymorphic in
     stage 3 as well.

6. **D1218. Diagnostics.** Keep E-PARTIAL-CALLBACK for fixed-row helpers.
   Drop its std-`map` note. Add the "only `List.map`'s callback can be
   partial so far" note for pure-callback std functions. Reword the E-PARTIAL
   notes (§7.2). No new codes.
   - **Recommended:** yes.

7. **D1219. D1182, cheaper partial calls.**
   - (a) **Recommended:** runner fast paths and a request node (A+B) in one
     lane, then the tail self-loop (C), each kept only with a benchmark
     showing at least 1.5x on both backends. Direct non-tail calls (D) only
     when a program needs them.
   - (b) Only A.
   - (c) Defer all of it.

   Reason: half the native time is allocation per call (§5.4), and none of
   A–C changes what a program means.

8. **D1220. The build plan.**
   - **Recommended:** lanes 3a–3e as in §7.4, after rule E lands, with 3a's
     acceptance including the 80 theorems unchanged and pure `map` within
     10%.

## 10. As built (lane 3a, 25 October 2026)

- **Library** (`core/Effect.sw`): `Divergence` (`Total`, `MayDiverge`),
  `CompD`, `doneD`, `bindDv`, `liftD`, `delayD`, as §2.1. They and the type
  are library-internal (`Elaborator::is_internal`, D1122). Their bodies are
  checked as plain terms, not in computation mode
  (`Elaborator::divergence_case_body`): each case is the computation it is.
- **Signatures** (D1214): `autobind` marks the auto-bound row variables used
  only bare; `signature_type` binds an implicit `%div.e : Divergence` right
  after each, and `effect_type` makes `{e} a` a `CompD %div.e e a`. Local
  definitions' signatures don't get one yet.
- **Rows** (`effects.rs`): `Row` has `div: Option<Value>`. `comp_parts`
  reads a stuck `CompD`; `done`, `bind_term`, `comp_type` build the `…D`
  forms; `lift` settles an unknown index (from the other side, else
  `Total`), then moves with `liftD`/`delayD`. A rigid index moved into a
  total row is E-PARTIAL.
- **Inference**: `unify::divergence_rule` solves `CompD ?d E B ≟ T`: a
  `Delay` gives `MayDiverge` and its row; anything settled gives `Total`
  and then the `CompIn` rule; a blocked side is put aside. Unsolved `?d`s
  default to `Total` with the row unknowns (`rows::default_rows`).
- **The re-check** (D1215): any body that fails with an index in its
  signature is checked again with `total_rows_only` (`retype_total`, which
  gives the pending definition its total type through the kernel's new
  `retype_def`). Where the first check failed is kept in
  `Elaborator::total_rows`: a caller's E-PARTIAL gets a label there and a
  note, and hover a line. Only in `group`; mutual groups retype in place.
- **Specialisation** (D1216): `specialise.rs` takes a list of driver types,
  `Effects` at `Empty` and `Divergence` at `Total`.
- **Printing**: `CompD d e a` prints `{e} a`, at `MayDiverge`
  `{Partial | e} a`; `doneD Total Empty v` prints `v`.
- `reject/partial-callback-std.sw` became `accept/partial-map-self.sw`.

### Lane 3c: messages, examples, docs (25 October 2026)

- **E-PARTIAL-CALLBACK** no longer points at `mapP`. For a std helper it
  says the helper "doesn't take partial callbacks yet" and that so far only
  `List.map`'s may be partial. For a helper whose row has abilities and a
  tail it says why (a handler can't run partial code). A fixed row keeps
  its "make it polymorphic in the rest of the row" note.
- **E-PARTIAL** (`partial_in_total`): when the partial thing is a call whose
  argument is a partial definition, the label is "`List.map` is partial
  here because its callback `collatzSteps` is". The note no longer says
  "add `Partial` to the enclosing function's type" alone: it adds "if it is
  a callback, the function taking it must allow a partial callback". A
  lambda given to a callback parameter that must finish gets a note about
  that parameter instead (`total_lambda_note`).
- **Function-type E-PARTIAL** (`partial_mismatch`): "a row variable like
  `e` never stands for `Partial`" is now about rows with abilities, and
  says a bare `{e}` may be partial.
- **E-TYPE-MISMATCH** for a named partial function given to a pure-callback
  parameter (`List.filter xs isTrivial`) gets a note
  (`total_callback_note`).
- **Examples**: `accept/partial-map-main.sw` (`main: {IO, Partial}`, nested
  `map`, tests); `reject/partial-map-total-caller.sw`,
  `reject/partial-filter.sw`, `reject/partial-filter-lambda.sw`,
  `reject/partial-map-fixed-row.sw`; the guide's `partial-map.sw`.
- **Ticks** (`crates/rt/tests/tick_counts.rs`,
  `a_partial_map_adds_no_ticks_of_its_own`): `map collatzSteps [3, 7, 27]`
  needs exactly 134 ticks on both runners, as the sum of the three calls.

Measured (`bench/effect-map/map.sw`, `map 1000000 10`, best of 5, shared
machine): before 1.059–1.083 s native, 0.565–0.596 s `--js`; after
1.057–1.082 s native, 0.592–0.603 s `--js`. The `fail` mode (a `{Fail}`
callback, generic code testing `d` per element) is about 2–9% slower:
before 3.49–3.75 s native, 3.51–3.58 s `--js`; after 3.83–4.08 s and
3.59–3.80 s.
