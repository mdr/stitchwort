# Proposal: handlers around partial code

**Status:** draft 1, 25 October 2026, for review (D1249). Nothing here is
built. Decisions D1254 to D1257 are at the end.

Tags, as in the other `Partial` notes: **[source]** read in the code,
**[ran]** run on today's build, **[web]** checked online (links in §6),
**[inferred]** reasoned but not run, **[speculative]** a guess.

## Contents

0. Summary
1. Where things stand
2. What it means (question 1)
3. Why it's sound (question 2)
4. Rows with abilities: lift stage 3's restriction too? (question 3)
5. How it runs (question 4)
6. Prior art (question 5)
7. The roguelike and `Terminal`, without fuel (question 6)
8. Build plan
9. What I couldn't verify
10. Decisions for Matt

## 0. Summary

**The problem.** A handler can't go around code that might not finish. So
the roguelike's game loop counts down 100,000 turns of fuel, only so that
its three handlers (input, randomness and, in tests, `IO.simulate`) can wrap
it (`games/rogue/NOTES.md`, item 4, ranked first of ten). Every interactive
program hits the same wall, and so will `Terminal.toIO` and
`Terminal.simulate` (D1246).

**The proposal, in plain words.** Let a handler wrap partial code, and say
in the result's type that it's still partial. Handling `Random` around a
`{Random, IO, Partial}` loop gives an `{IO, Partial}` result. The handler
sees each operation and the rest of the program, exactly as it does today;
the program's own recursion passes straight through it. Nothing that runs
forever can become "finished" by being handled: `Partial` itself still has
no operations and no handler.

**What it takes.**
- **One new kernel constant, `foldD`** (D1254). It's the handler fold for a
  partial computation, like the five `Delay` constants of stage 1: no
  definition, no computation rules, and its result is always a `Delay`, so
  only the runner ever runs it. The elaborator uses it where it uses
  `foldComp` today, when the handled code is partial.
- **A divergence index on rows with abilities** (D1255), extending stage 3's
  rule from `{e}` to `{A | e}`. Then `Fail.toResult`, `IO.simulate`,
  `Each.collectIn`, the roguelike's `fromLines` and `seeded`, and the future
  `Terminal.toIO`/`Terminal.simulate` all take partial programs **with no
  change to their source**, while their total uses, and the proofs about
  them, compute exactly as today.
- **A `Handle` frame** in the three runners' stepping machines (§5).

**Ticks.** A handler adds none. Each recursive call is still exactly one
tick; code in a handler's clauses ticks for its own recursion (§2.3).

**Soundness, briefly.** Stage 1's argument covers `foldD` unchanged: every
`Delay` type can be read as a one-element set, and `foldD`'s result is a
`Delay`, so adding it can't prove anything false. The reason for the
restriction in partial.md §7.3.8 was representational ("there's nothing to
fold in a `Delay`"), and the knot of §8.3/§10.4 needs total code that can
look inside a `Delay`, which still doesn't exist (§3).

**The plan.** Four lanes: the executable model first, then kernel +
reference runner + elaborator, then the native and JS runners, then the
divergence index on rows with abilities and the std/guide/roguelike follow-up
(§8).

## 1. Where things stand

### 1.1 The restriction, in the code

`handle` is elaborated in `crates/elab/src/effects.rs`, `fn handle`
(line 3704) **[source]**. It produces `foldComp done step body`, where the
carrier (what each clause returns) is `r = comp_type(out, t)`: `{out} t` as
a core type. When `out` is partial, `r` is already a `Delay`
(`call_term = if out.partial`, line 3948, forwards an operation with
`bindD (lift (Call …)) …`). So a handler *in* a partial context works today;
what's refused is a partial *handled* computation. Line 3812:

```rust
// The handled computation is total even in a partial context: a
// handler is a fold over a `Comp`, and there's nothing to fold in a
// `Delay` (docs/proposals/partial.md §7.3.8).
let inner = Row { labels: inner_labels, tail: rest.tail.clone(), partial: false, div: None };
```

The kernel enforces the same thing independently: `foldComp` takes a
`Comp`, and a partial computation is a `Delay` (partial.md §7.9).

### 1.2 The errors, today **[ran]**

On today's build (`da19ab90`), with scratch files.

A handler written in place:

```stitchwort
def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)

def caught (n: Nat): {Partial} Result Nat Text :=
  handle countdown n with
    | return x => Ok x
    | Fail.stop msg, k => Err msg
```

```text
[E-PARTIAL] Error: a computation that might not finish can't run here
  8 │ ╭─▶   handle countdown n with
 10 │ ├─▶     | Fail.stop msg, k => Err msg
    │ ╰─────── `countdown` is `Partial`: it might not finish
    │     Note: the computation a handler handles can't be `Partial`: a handler folds over
    │     every way a computation can go, which needs it to finish
```

A std handler (`Fail.toResult (() => countdown n)`):

```text
[E-PARTIAL] Error: a computation that might not finish can't run here
 7 │ def caught (n: Nat): {Partial} Result Nat Text := Fail.toResult (() => countdown n)
   │                                                                        ─────┬─────
   │                                                    `countdown` is `Partial`: it might not finish
   │ Note: … if it is a callback, the function taking it must allow a partial callback
```

`IO.simulate` around a partial loop, in a test:

```stitchwort
def echo(): {IO, Partial} () :=
  match IO.readLine() with
    | None => ()
    | Some line =>
      IO.print line
      echo()

test "echo" := (IO.simulate ["a", "b"] echo).fst == ["a", "b"]
```

```text
[E-PARTIAL] Error: a partial function can't be used where a total one is expected
 11 │ test "echo" := (IO.simulate ["a", "b"] echo).fst == ["a", "b"]
    │                                        ──┬─
    │                                          ╰─── this might not finish: its type says `Partial`
    │ Note 1: … a row with abilities, `{… | e}`, is total because a handler can't run
    │ partial code, so a function taking it can't be given a partial one …
```

And even a handler whose own type says `Partial` (`seeded (seed: Nat)
(prog: () → {Random, Partial | e} a): {Partial | e} a`, a copy of the
roguelike's) is refused at its `handle`, with the first message.

### 1.3 What the restriction costs

- **The roguelike** (`games/rogue/src/Rogue/Rogue.sw`): `play: Nat → State →
  {IO, Input, Random} State` counts down `maxTurns = 100000`, and `ending`
  has a case "The game ran out of turns." that exists only because of the
  fuel. `readCommands` has its own fuel too (`linesPerCommand = 1000`).
- **The guide** says it out loud (chapter 8, after `sumLines`): "A handler
  still can't go around partial code, so `Fail.toResult` can't catch a
  failure from inside `sumLines`: only `main` can leave it unhandled."
- **Stage 3** kept `{A | e}` total *because of* this restriction
  (partial-stage-3.md §2.2), so no std handler takes a partial program.
- **`Terminal`** (D1246): a library ability interpreted into `IO` by
  `Terminal.toIO` and tested with `Terminal.simulate`. A game's loop is
  `Partial` (terminal-io.md §1). Without this note, neither handler could
  run it.

## 2. What it means (question 1)

### 2.1 The rule

Handling an ability `A` around `prog: () → {A, Partial | e} r` with a
handler whose clauses are total gives `{Partial | e} r'`. Generally: the
handled computation may be partial, and then the handler's output row is
partial too. Clauses are elaborated in that partial output row, as they are
today whenever the output is partial, so they may run partial code as well.

`Partial` never appears in the ability handled, never stands for a row
variable's abilities, and is never removed: it moves from the handled row
to the output row, unchanged.

### 2.2 In plain words: what a handler does to a partial program

A partial program runs as a sequence of steps. Each step ends one of three
ways: it finished with a value; it made a recursive call (a tick, and the
rest is suspended); or it performed an operation and waits for the answer.
A handler wrapped around it watches those step endings:

- **Finished with `v`:** the handler runs its `return` clause on `v`.
- **A tick:** the handler passes the tick straight out, and stays wrapped
  around the rest. It doesn't see recursion at all.
- **An operation of `A`:** the handler runs that operation's clause, giving
  it the argument and `k`, the rest of the program from that point, still
  wrapped in the same handler (a *deep* handler, as today).
- **Any other operation:** forwarded outward, with the answer passed back,
  as today.

### 2.3 Precisely: one new constant and its step equation

The kernel gets one constant beside stage 1's five (partial.md §7.2):

```
-- The handler fold for a partial computation. Its result is a `Delay`: a
-- handler around partial code is partial.
def Effect.foldD: [op1: Type] → [res1: op1 → Type] → [op2: Type] → [res2: op2 → Type] →
    [a b: Type] →
    (done: a → Delay op2 res2 b) →
    (call: (o: op1) → (res1 o → Delay op2 res2 b) → Delay op2 res2 b) →
    Delay op1 res1 a → Delay op2 res2 b
```

It's `foldComp`'s type with every carrier `r` replaced by `Delay op2 res2 b`.
That's exactly the carrier the elaborator already builds for a partial
output row (`comp_type(out, t)` is `Delay (ops out) (res out) t`), so the
elaborator's change is choosing `foldD` instead of `foldComp` and no longer
forcing the handled row total (§8, lane B). State-passing handlers (the
roguelike's `seeded`, `IO.simulate`) are covered: their `b` is a function
type, `Nat → {Partial | e} a`, as their `t` is today **[source]** (the
carrier is `comp_type(out, t)` for any `t`).

The runtime meaning, in the notation of partial.md §7.4.2 (`step` returns a
*segment*: a well-founded tree of operations ending in `Now v` or
`Later rest`):

```
step (foldD done call d) = foldSeg done call (step d)

foldSeg done call (Done (Now v))    = step (done v)
foldSeg done call (Done (Later d')) = Done (Later (foldD done call d'))
foldSeg done call (Call o r)        = step (call o (y => foldD done call (resume (r y))))
```

`resume s` is stage 1's: it turns the rest of a segment back into a `Delay`
without adding ticks. The handler's `call` sees every operation of `op1`;
today's elaborator already makes it dispatch `A`'s operations to the
clauses and forward the rest with `handlePlus` (the `Builtin::HandlePlus`
call in `fn handle`) **[source]**, and that's unchanged.

### 2.4 Ticks

- **A handler adds no ticks.** The middle equation passes a `Later` through
  as exactly one `Later`, as `mapSig` and `tie` do (partial.md §7.4.2).
- **Each recursive call is still exactly one tick.** A partial function's
  requests are answered by its own `tie`, inside the handled `Delay`; the
  handler is outside it and never sees a request (they're in the private
  `Rec` row, which can't reach a handler: E-PARTIAL-ESCAPE).
- **Handled operations are free**, as all operations are (§7.4.3).
- **Clauses tick for their own recursion**, as any partial code does.
  A clause that calls `k` twice runs the rest of the program twice, and
  both runs' ticks count.

So `seeded 0 (() => play 0)` over five input lines takes exactly as many
ticks as `play` makes recursive calls (five), with or without the handler
**[inferred]** from the equations; lane A's model checks it (§8).

### 2.5 `return` clauses

Run once, when the handled program finishes, on its result, as today. If
the program never finishes, the `return` clause never runs. A `return`
clause may itself run partial code (it's elaborated in the partial output
row).

### 2.6 Deep handlers

`k` is `y => foldD done call (resume (r y))`: the rest of the program,
under the same handler. That's what `foldComp` gives today, so every
handler in std and the examples keeps its meaning.

### 2.7 Resuming zero times, or many

- **Zero** (`Fail.toResult`'s `stop` clause, `Abort`): the rest of the
  program is dropped, with whatever recursion it had pending. The result can
  finish even though the program "would have" looped:
  `Fail.toResult (() => { Fail.stop "no"; spin 0 })` finishes, with
  `Err "no"`, but its type still says `Partial`. That's the right type: no
  checker can see this in general, as the OOPSLA 2021 example in §6 shows.
- **Once** (state, `seeded`, `fromLines`, `IO.simulate`): the usual case.
- **Many** (`Each.collectIn`, `Each.both`): each call of `k` runs the rest
  of the program from that operation to its end, one after another. For
  `List.append (k True) (k False)`, all of the `True` branch's ticks and
  operations come first, then the `False` branch's. If the `True` branch
  never finishes, the `False` branch never runs and the handler never
  finishes. That's depth-first search over a possibly-endless tree: well
  defined, sometimes useless. Koka gives multi-shot handlers over
  divergent code the same reading (`choice-all` composed with `pstate`, both
  typed `div`, §6) **[web]**. Fair interleaving of branches would need
  observation by total code (partial.md §10.1), which this note doesn't add.
  Recommendation: allow it (D1256).

## 3. Why it's sound (question 2)

### 3.1 The original reason for the restriction

partial.md gives two reasons, and §10.4 a third concern:

1. **§7.3.8: "a handler is a fold over `Comp`, and there's nothing to fold in
   a `Delay`."** This is about representation: no *existing* constant can
   take a `Delay` apart. `foldD` is a new constant whose result is again a
   `Delay`, so it doesn't let total code take one apart either.
2. **§8.2: "a handler that acknowledges every step."** A handler for
   `Partial` itself that answered each tick would turn an endless
   computation into a total one. This stays impossible: `Partial` has no
   operations, a handler can't name it, and `foldD` never removes `Partial`
   (its result is a `Delay`). The soundness tests for it stay (§8).
3. **§10.4: the knot.** A handler whose clause gets a continuation leading,
   past a tick, back into the handler could *step its own continuation's
   result*, which is §8.3's `pfixBad` again. That needs total code that can
   step a `Delay` (§10.1's `runFor`). None exists, and this note adds none:
   a clause can only *sequence* `k y` (with `bindD`), never look inside it.
   partial-stage-2.md §10.4 reached the same verdict: "Lower [risk] than
   partial.md §10.4 suggests, *as long as 10.1 isn't built*". **If §10.1 is
   ever built, `foldD` must be part of its productive-observer argument.**

Does stage 3's `CompD` change any of this? No **[inferred]**. `CompD` is an
ordinary definition by cases (partial-stage-3.md §3.2); it adds no way to
look inside a `Delay`. Stage 3 *relied* on the restriction (to keep
`{A | e}` total), which is §4's question, not a soundness one.

### 3.2 Principle 1: no hidden divergence

- `foldD`'s result is a `Delay`, which messages print as `{Partial | …}`.
  From there, everything is stage 1: total code can't run it (E-PARTIAL),
  and the caller must say `Partial` too. The kernel checks this
  independently of the elaborator: a total type is a `Comp` (or `CompIn`)
  type, and a `Delay` doesn't convert to one (partial.md §7.9).
- **No total type escapes.** The handler's output type is whatever
  `comp_type` makes of a partial row: a `Delay`. The carrier `b` may be
  anything (a function type for state handlers), but it's always *inside* a
  `Delay`, so nothing of type `b` can be had from it by total code. The
  constant's type is checked exactly at admission (`define_primitive`'s
  `expected`, `crates/core/src/partial.rs` line 173) **[source]**, so a
  prelude giving `foldD` a carrier that isn't a `Delay` is refused
  (E-BUILTIN); lane B adds that test.

### 3.3 Principle 2 and consistency: the kernel stays total

partial.md §7.8's argument, unchanged: interpret every `Delay op res a` as a
one-element set. `foldD`'s type ends in a `Delay`, so in that model it's the
constant function to the one element. It never needs an `a` or a `b`. So the
model still exists, and no closed proof of `Void` is added **[inferred]**,
by the same argument the review accepted for stage 1 [RV §2].

`foldD` has no computation rule, so conversion treats its applications as
neutral, as `pfix`'s: a type that mentions `Fail.toResult (() => countdown
3)` stops at `foldD …`, and `rfl` across it fails as
`soundness/partial-unfold.sw` does. Checking never runs a handled partial
program, and tests run it only in `stitchwort test` (D1183).

### 3.4 Each step still ends

The runner's guarantee that a single step of a `Delay` ends (so its budget
is meaningful) extends **[inferred]**. Stepping `foldD done call d` steps
`d` to a segment (which ends, by stage 1), then may step clause code, which
may call `k`, which steps a *strict subtree* of that segment. A clause that
calls `k` twice explores the segment twice. So a step's work is bounded by
induction on the segment, a well-founded tree; it may be large, which the
per-step budget already handles (partial.md §7.5).

### 3.5 Proofs about handlers

- **Handlers proved about today stay provable for total programs**, if the
  divergence index of §4 is used: at `Total`, the handler's fold is
  `foldComp`, by computation, as `List.map` at `Total` is today
  (partial-stage-3.md §3.3). 27 `theorem` lines in std mention
  `Fail.toResult`, `toOption`, `orElse`, `recover`, `context`, `orFail`,
  `toAbort`, `IO.simulate` or `collectIn` **[ran]** (grep); lane D's gate is
  that they check with no edits.
- **Handled partial programs have nothing to prove**, as in stage 1
  (partial.md §7.7). Testing them is D1183's business.
- **Without §4**, a handler that takes partial programs must say
  `{A, Partial | e}` in its signature and is *always* a `foldD`, so nothing
  can be proved about it even for total programs. That's the main reason to
  do §4.

### 3.6 What the argument doesn't cover

As for stage 1: that the runners run the intended program. That's tested
against the model's equations (§2.3) with complete traces: operations,
replies and ticks, on all three runners (§8).

## 4. Rows with abilities: lift stage 3's restriction too? (question 3)

### 4.1 The choice

Stage 3 gave a divergence index `d` only to row variables used *bare*,
`{e}`, "because handlers can't run partial code" (partial-stage-3.md §2.2).
With `foldD`, that reason is gone. Two scopes:

- **Narrow (D1254 alone).** In-place `handle` around partial code works, and
  so does a handler whose signature says `Partial` explicitly:
  `seeded (seed: Nat) (prog: () → {Random, Partial | e} a): {Partial | e} a`.
  Such a handler's result is *always* partial, even for a total program,
  and nothing about it can be proved. Every std handler would need a second,
  partial copy (`Fail.toResultP`, `IO.simulateP`, …), against D1110's "one
  function" spirit.
- **Wide (D1254 + D1255).** Extend D1214's rule: a row variable `e` gets a
  divergence index when every occurrence of it is in a row, bare `{e}` *or
  with abilities* `{A, B | e}` (not when it's a data type's argument, as in
  `Checker e`). Each such row means `CompD d (A, B | e)`. Then:

| Signature (unchanged source) | Today | Wide |
|---|---|---|
| `Fail.toResult (prog: () → {Fail \| e} a): {e} Result a Text` | total only | partial if `prog` is |
| `IO.simulate (input) (prog: () → {IO \| e} a): {e} Pair …` | total only | partial if `prog` is |
| `Each.collectIn (prog: () → {Each \| e} a): {e} List a` | total only | partial if `prog` is |
| `Rogue.seeded`, `Rogue.fromLines` | total only | partial if `prog` is |
| `Terminal.toIO`, `Terminal.simulate` (D1246) | – | partial if `prog` is |
| `Each.collect (prog: () → {Each} a): List a` | total only | total only (no row variable) |

**Recommendation: wide (D1255),** built as its own lane after the narrow
part (§8). It's what makes `Terminal.simulate` and `IO.simulate` usable
around a partial game loop while staying provable for total programs.

### 4.2 What the wide scope needs

The pieces stage 3 named and deferred (partial-stage-3.md §2.2: "a
divergence index on every row with a tail, and `translate`/`mapSig`
variants for each"):

```
-- The handler fold at either divergence (in core/Effect.sw, library-internal).
def Effect.foldCompD … : (d: Divergence) → … → CompD d (handled row) a → CompD d out b
  | Total,      … => foldComp done call      -- today's handler, by computation
  | MayDiverge, … => foldD done call

-- Moving a computation between rows with abilities.
def Effect.translateD … : (d: Divergence) → SigMap … → CompD d from a → CompD d to a
  | Total,      m, c => translate m c
  | MayDiverge, m, c => mapSig m c
```

- `CompD d (A | e) a` at `Total` must compute to today's `{A | e} a`, which
  is `Comp (Plus A (rowOp e)) … a`. Building the row as
  `Ops (Plus A (rowOp e)) (PlusRes …)` gives that, since `CompIn (Ops op
  res) a` is `Comp op res a` **[source]** (`core/Effect.sw`, `CompIn`).
- **D1215's fallback carries over**: a body that needs `e` total (a clause
  passing `k` to a pure helper, as `Each.collect`'s `Each.both` does) is
  checked again with `e` total, as for bare rows today.
- **Specialisation** (D1216): handlers specialise at `Total` like `map`, so
  the effect runtime's fast paths (state-handler fusion, closed signature
  maps, lazy resumption) keep running total handlers unchanged **[inferred]**.
  At `MayDiverge` the generic code runs, through `foldD`.
- **Messages**: E-PARTIAL-CALLBACK's note "a handler can't run partial code"
  and `partial_mismatch`'s note about `{… | e}` go.

### 4.3 Not in scope

- **Partiality as a value programs can name** (partial.md §10.7). `d` stays
  library-internal (D1122).
- **Data types with row parameters** (`Checker e`, D1160) stay total.
- **Observing a `Delay` with fuel** (§10.1): not needed (§5.4).

## 5. How it runs (question 4)

### 5.1 The three runners

All three already step a `Delay` with an explicit stack of frames on the
heap (`Bind`, `Map`, `Tie`, `Await`): `crates/core/src/step.rs` (reference),
`crates/rt/src/run.rs` (native), and `crates/js/src/run.rs`'s copy for
`run --js` **[source]**. Each gains:

- **a `Delay` form** for `foldD done call d` (the runtime's `Delay` enum in
  `crates/rt/src/value.rs` has `Now`, `Lift`, `Bind`, `Map`, `Pfix`);
- **a `Handle(done, call)` frame**, pushed when stepping it; `Now v` reaching
  it pops it and runs `done v`, and a `Later` passes it by;
- **capture at an operation**: an operation reaching a `Handle` frame takes
  the frames above it as the continuation, and `call o k` runs with `k` a
  runtime value holding them. Applying `k y` pushes the `Handle` frame and
  the captured frames back and returns `y` to the top.

Operations from the handled program pass `Tie` and `Await` frames on the way
to the `Handle` frame, as they pass them on the way to the runner today.
`Await` frames record positions relative to their `Tie` (`marks`, `back`)
**[source]**, so lane B must check that capturing and restoring a slice of
frames keeps them right; the model (lane A) is where that's settled first.

### 5.2 Multi-shot: copying the captured frames

The reference and native steppers keep frames in a `Vec<Frame>`, which is
changed in place **[source]**. A `k` called once can move its frames back;
one called twice must copy them, which costs time in proportion to how
deep the handled program is at that operation **[inferred]**. The effect
runtime for total code doesn't have this cost: its continuations are a
persistent linked list, "so a `Resume` can be resumed any number of times,
and later" (`crates/rt/src/effect.rs`, module comment) **[source]**. Copying
is simple and only multi-shot pays for it; a persistent frame list for
`Delay` is a later optimisation if a program needs it.

### 5.3 Stack safety

Frames stay on the heap, so nothing nests in Rust or JS **[inferred]**:
- a loop inside a handler (`seeded 0 (() => play 0)`) makes its recursive
  calls under its own `Tie`, above the `Handle` frame; tail calls keep no
  frame, as today, so the loop runs in constant space;
- an operation captures the few frames between it and the handler, and a
  clause that resumes in tail position (`resume (current + 1) (current + 1)`
  under a state function) leaves nothing below;
- a handler in a loop (`handle` inside a partial function's body) pushes a
  frame per entry and pops it when the handled part finishes.

Lane C's acceptance tests: a million handled operations and a million ticks
under a state handler, natively and with `--js`, as stage 3 measured `map`.

### 5.4 `IO.simulate` around a partial `main`, and tests

With the wide scope (D1255), `IO.simulate input main` for a partial `main`
has type `{Partial} Pair (List Text) ()`, and a test using it is a partial
test (D1183): `stitchwort test` steps it to its result, with no tick limit.
So the roguelike's play-through tests keep their source, and their
`simulateGame` loses the fuel inside it (§7).

The brief asked about a tick limit for such tests. D1183 decided tests have
none ("If it loops forever, that's just a bug and an acceptable risk"), and
a game loop driven by scripted input ends when the input does (the
roguelike quits at end of input). So no limit is proposed (D1257). The Rust
tests keep `Session::simulate`'s 1,000,000-tick limit (partial.md §9.4).

### 5.5 `build --js` exports

Unchanged: exports can't mention `Delay` (E-JS-PARTIAL), and inside an
export `build --js` erases every `Delay` constant's call to one token
without computing its arguments (partial.md §7.6, `def_call`)
**[source]**. `foldD` joins that list.

## 6. Prior art (question 5)

All **[web]**, checked 25 October 2026.

- **Koka.** `div` is an effect in the row, "if a function may not terminate
  the effect is `div`" ([book](https://koka-lang.github.io/koka/doc/book.html)),
  and it's declared with no operations: `pub type div :: X`
  ([std/core/types.kk](https://raw.githubusercontent.com/koka-lang/koka/master/lib/std/core/types.kk)).
  Handlers go around divergent code and keep `div` in the result: the book's
  state handler is `fun pstate( init : a, action : () -> <state<a>,div|e> b ) : <div|e> (b,a)`.
  Multi-shot too: `choice-all` (`resume(False) ++ resume(True)`) composed
  with `pstate` is typed `div (list<bool>,int)`. This is the design here,
  almost word for word. Whether `div` can be handled isn't stated; with no
  operations there's nothing to handle (not verified).
- **F\*.** "Tot computations cannot rely on Dv computations", and "it
  should be impossible to turn a `e:Dv t` into a term of type `Tot t`"
  ([Div chapter](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).
  For user effects layered over divergence: "An indexed effect F may
  optionally be marked divergent … However, reification of such effects
  results in a Div computation to capture the fact that this computation may
  diverge" ([Rastogi et al., *Programming and Proving with Indexed
  Effects*](https://fstar-lang.org/papers/indexedeffects/indexedeffects.pdf)).
  Their algebraic effects are a tree with a handler that gets the
  continuation (`handle_tree`). Handling divergent code gives divergent
  code, as here.
- **Idris 2.** Totality is per definition, not in types: "To be recorded as
  total, a function f must: … Not call any non-total functions"
  ([tutorial](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)).
  So a handler around partial code is simply not total. Same outcome,
  without a type.
- **Interaction Trees (Rocq).** `interp` takes a handler `h : E ~> M` that
  maps each event to a monadic action and never sees the continuation;
  `interp` applies `k` itself, through `iter`, and needs `MonadIter M`
  ([Interp.v](https://raw.githubusercontent.com/DeepSpec/InteractionTrees/master/theories/Interp/Interp.v),
  [Basics.v](https://raw.githubusercontent.com/DeepSpec/InteractionTrees/master/theories/Basics/Basics.v);
  [Xia et al.](https://arxiv.org/abs/1906.00046)). `stateT`, `readerT` and
  `optionT` have `MonadIter` instances, so state and failure handlers work
  over divergent trees. That's why partial.md §10.4 proposed
  `interp`-style handlers. Here clauses *do* see `k`, which ITrees avoid
  because Rocq code can observe an itree; Stitchwort's total code can't
  observe a `Delay` (§3.1), so the full deep-handler form is safe for now.
- **Agda.** The delay monad has `now` and `later` and a coinductive `bind`
  ([Codata/Sized/Delay.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Codata/Sized/Delay.agda)).
  I found no `DelayT` transformer in agda-stdlib (not verified either way).
- **Lean 4.** `partial` functions are "opaque constants" in the kernel, and
  "All that is required for soundness is that their return type is
  inhabited"; `partial_fixpoint` is "more powerful if the function's return
  type is a monad that is an instance of Lean.Order.MonoBind, such as
  Option" ([reference manual](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)).
  `StateT`, `ExceptT`, `OptionT` and `ReaderT` over such a monad are
  instances ([Order/Basic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Internal/Order/Basic.lean)),
  so partiality survives transformers. Same outcome: wrapping keeps
  partiality.
- **A handler can make looping code finish.** Karachalias et al. (OOPSLA
  2021, [doi](https://doi.org/10.1145/3485479)), §4: a recursive `go` that
  performs `Next n` before each call "seems to diverge. Yet, with the
  provided handler, its argument steadily increases and evaluation
  eventually terminates." A type system can't see this in general, which is
  why the result stays `Partial` (§2.7).

**The pattern:** every system that tracks divergence in types (Koka, F\*)
keeps it in the result of handling; systems that track it per definition
(Idris, Lean) reach the same place by making the wrapper partial too.
None lets a handler remove it.

## 7. The roguelike and `Terminal`, without fuel (question 6)

### 7.1 `play` without fuel

Today (`games/rogue/src/Rogue/Rogue.sw`) **[source]**:

```stitchwort
def maxTurns: Nat := 100000

def playGame (state: State): {IO, Input, Random} State :=
  draw state
  play maxTurns state

def play: Nat → State → {IO, Input, Random} State
  | 0, state => state
  | Succ remaining, state =>
    if state.phase == Playing then
      let command := nextCommand()
      let next := step state command
      draw next
      play remaining next
    else state
```

After D1254 and D1255 (sketch, not run):

```stitchwort
def main(): {IO, Partial} () :=
  let final := fromLines (() => seeded defaultSeed (() => playGame initialState))
  IO.print (ending final)

def playGame (state: State): {IO, Input, Random, Partial} State :=
  draw state
  play state

-- One turn per command, until the game is won, lost or given up.
def play (state: State): {IO, Input, Random, Partial} State :=
  if state.phase == Playing then
    let command := nextCommand()
    let next := step state command
    draw next
    play next
  else state
```

- `fromLines` and `seeded` keep their source: their rows `{Input, IO | e}`
  and `{Random | e}` get a divergence index (D1255), and here it's
  `MayDiverge`.
- `maxTurns` and the "ran out of turns" ending go (the `Playing` case of
  `ending` stays, since its type doesn't know the loop ended; it can say
  so). `readCommands` can lose `linesPerCommand` the same way, becoming
  `{IO, Partial}`.
- The tests keep their source. `simulateGame` becomes
  `{Partial} (List Text, State)`, and its tests become partial tests
  (D1183). The end of the scripted input is `Quit`, so every test ends.
- The proofs (`Rogue.Proofs`) are about `step`, which is total and
  unchanged. `Proofs/Step.sw` is about `seeded` on a one-turn computation,
  which is total, so `seeded` computes as today there **[inferred]**; lane
  D's roguelike follow-up checks it.

### 7.2 `Terminal`, as a library ability (D1246)

```stitchwort
ability Terminal where
  readKey: () → {Terminal} (Option Key)
  draw: List Text → {Terminal} ()

-- For real: each operation as a few basic `IO` operations.
def Terminal.toIO (prog: () → {Terminal, IO | e} a): {IO | e} a := handle prog() with …

-- For tests: scripted keys in, frames out.
def Terminal.simulate (keys: List Key) (prog: () → {Terminal | e} a): {e} Pair (List (List Text)) a
```

With D1255 both take a partial game loop with these exact signatures, and a
proof about `Terminal.simulate` on a total program (say, that it records one
frame per `draw`) works as `IO.simulate`'s do. With D1254 alone they'd need
`{Terminal, Partial | e}` and would always be partial. The terminal note
(terminal-io.md) gets revised after this one, as the brief says.

## 8. Build plan

Each lane is stage-sized; each runs only the tests it names.

**Lane A: the model.** Add `foldD` to `crates/partial-model`: the reference
equations of §2.3, the machine (`Handle` frame, capture, copy on second
use), and programs with complete expected traces:
- `Fail.toResult` around `countdown 5` (stops at 3: `Err`, 2 ticks) and
  `countdown 2` (`Ok 0`, 2 ticks);
- a state handler around `play` over 5 inputs (ticks = 5, the same as
  unhandled);
- `collectIn` with `fork` around a partial search (ticks of both branches,
  in order); a first branch that loops (stopped at the tick limit, second
  branch never run);
- a handler inside a partial function's body (capture across `Tie` and
  `Await`); nested handlers; a clause that runs partial code;
- the model's machine identical to its equations on each, and on its
  generated programs extended with `foldD`.

**Lane B: kernel, reference runner, elaborator** (D1254).
- Kernel: `foldD` in `core/Effect.sw` beside `pfix`; `Primitive::FoldD` and
  its exact type in `crates/core/src/partial.rs`; hashing; E-BUILTIN tests
  (a carrier that isn't a `Delay`; a result type `b` with no `Delay`).
- Reference runner: `crates/core/src/step.rs`, as lane A's machine; trace
  tests against the model in `crates/driver/tests/partial.rs`.
- Elaborator: `handle` with a partial handled row uses `foldD` and makes
  the output row partial (a total expected type stays E-PARTIAL, with a
  message saying the handled code is partial). Explicit
  `{A, Partial | e}` signatures work.
- Examples: `reject/partial-handled.sw` becomes accept (in
  `accept/partial-handlers.sw` with `caught`, explicit-`Partial` `seeded`
  around a loop, tests); soundness: a handled partial program in a total
  context (E-PARTIAL), a handler naming `Partial` (refused, as today), `rfl`
  across a handled partial program (E-REFL).

**Lane C: native and JS runners.** `crates/rt` (`Delay::Fold`, the frame,
capture/copy, lowering of `foldD`), `crates/js/src/run.rs` (the same), and
`build --js`'s erasure. Tests: the model's traces on both (as
`tick_counts.rs`); a million handled operations and a million ticks under a
state handler, native and `--js`, stack-safe; a recorded timing for each.

**Lane D: rows with abilities** (D1255). `autobind`/`signature_type` give
`{A | e}` rows an index; `foldCompD`, `translateD`; inference and the
D1215 fallback as for bare rows; specialisation at `Total`; message notes.
Gate: the 27 std theorem lines of §3.5 and every existing example check
with no edits; `reject/partial-row-variable.sw` becomes accept (an
`IO.simulate` of a partial program, as a test).

**Follow-ups** (fresh lanes, after D): guide chapter 8 (the sentence after
`sumLines` becomes a `Fail.toResult` around it) and DESIGN.md §5 rule 4
("`Partial` has no operations and no handler may handle it; a handler
around partial code is partial"); the roguelike without fuel (§7.1); then
the terminal note's revision.

## 9. What I couldn't verify

- **Ticks and traces** of §2.4 and lane A's list are from the equations,
  not run: there's no `foldD` to run yet.
- **Stack safety and multi-shot cost** (§5.2, §5.3) are inferred from the
  machines' structure.
- **That `Await` frames survive capture and restore** (§5.1) is an open
  question for lane A.
- **That `?d` inference works for rows with abilities** as it does for
  bare rows (§4.2) is inferred from stage 3's build.
- **Koka's `div`** is not stated anywhere I found to be unhandleable; that
  it has no operations is verified. I found no `DelayT` in agda-stdlib.

## 10. Decisions for Matt

**D1254. Let a handler wrap partial code, with the result still partial?**
Context: one new kernel constant, `foldD`, the handler fold for a partial
computation. Like stage 1's `Delay` constants it has no definition and only
the runner runs it, and its result is always partial, so nothing can turn
looping code into "finished" code. `Partial` itself still can't be handled.
DESIGN.md §5 rule 4 is reworded to say so. In-place `handle` and handlers
that say `Partial` in their own type work. Recommendation: **yes**.

**D1255. Let rows with abilities, `{A | e}`, be partial too, as `{e}` can
since stage 3?** Context: then std's handlers (`Fail.toResult`,
`IO.simulate`, `Each.collectIn`), the roguelike's `seeded` and `fromLines`,
and `Terminal.toIO`/`Terminal.simulate` take partial programs with no
change to their source, and stay provable for total ones. Without it, each
would need a second, always-partial copy that nothing can be proved about.
It's a lane of its own, after D1254. Recommendation: **yes**.

**D1256. Allow handlers that resume more than once (`Each.collectIn`)
around partial code, running each resumption to its end before the next?**
Context: a search's first branch runs completely before the second starts;
if it loops, the second never runs. Koka does the same. The alternative is
to refuse it, which gives nothing back. Recommendation: **yes**.

**D1257. Keep tests without a tick limit (D1183) for handled partial
programs, such as `IO.simulate` around a partial game loop?** Context: a
scripted game ends when its input runs out, so a test of it ends; a test
that loops is a bug, as D1183 says. A limit would need total code that can
observe a partial program (partial.md §10.1), a much bigger change.
Recommendation: **yes** (no limit).
