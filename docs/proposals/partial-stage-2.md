# Proposal: `Partial`, stage 2 and after

**Status:** stage 2 built (D1179, §6 "As built"); the rest is a design note, 25 October 2026.
It follows [partial.md](partial.md): stage 1 is built (§9.4 there), and
§10 there lists the someday/maybe options. This note checks where stage 1
stands with real programs, looks at each option again, and recommends what
to build next.

Claims are marked like this:
- **[ran]**: run for this note with `target/release/stitchwort` built from
  `main` at `de7b4f50`, Node 22.23.3, Apple M4 Pro, on a shared machine.
  Times are single runs.
- **[source]**: read in the code.
- **[inferred]**: my reasoning, not tested.

Claims about other languages link to a source I opened for this note.

## 0. Summary

**What works.** Partial loops that read input, recursion with no known
bound, `match` inside partial code, and calls between partial functions all
work. They're stack-safe and reasonably fast on both backends (§1.2).

**What's missing, in order of how often a real program hits it.**
1. **A partial `main` can't use `Fail`** (§1.1, G1). Any loop that parses
   its input with `Text.toNatOrFail` is refused, and there's no workaround
   that keeps the exit status.
2. **Std's higher-order functions can't take partial callbacks** (G3).
   `List.map collatzSteps xs` is refused, so programs hand-write a `mapP`,
   which costs one tick per element and runs about 3x slower.
3. **There's no way to test a partial function** (G4), except by keeping a
   hand-written fuelled copy that can drift from the real one.
4. **No handler can go around partial code** (G2), so a partial loop can't
   keep a counter in a `State`-style ability.

**Recommendation.**
- **Stage 2:** `main: () -> {IO, Fail, Partial} ()`. The runner performs
  `Fail.stop` itself, as it performs `IO.print`. This is one lane, with no
  kernel change and no new trusted code in the logic (§3).
- **Stage 3, after a design note of its own:** row variables that may stand
  for partial rows, so the one `List.map` (D1110) also takes partial
  callbacks. This is D1121's "revisit when a callback needs to be partial"
  (§4).
- Two small fix-ups can go into any lane (§1.1, G5).

Decisions for Matt are in §5.

## 1. Where stage 1 stands

### 1.1 Realistic programs

Each program is in full below, or quoted from the repository. The scratch
files aren't committed.

| # | Program | Result |
|---|---|---|
| G1 | A partial read loop in a `main` that fails on bad input | **Refused** (E-MAIN-TYPE) |
| G1′ | The same loop, with `Fail.toResult` around a partial search | **Refused** (E-PARTIAL) |
| G2 | A counter handler (`runCounter`) around a partial echo loop | **Refused** (E-PARTIAL) |
| G3 | `List.map collatzSteps [3, 7, 27]` in `main` | **Refused** (E-PARTIAL) |
| G3′ | A partial function mapping itself over its children with `List.map` | **Refused** (E-PARTIAL-CALLBACK, with a confusing note) |
| G3″ | `List.filter` with a partial predicate | **Refused** (E-TYPE-MISMATCH) |
| G4 | A test of `collatzSteps 27` | **Refused** (E-PARTIAL); the only route is a fuelled copy |
| ok | A read-eval-print loop written directly, with nested `match` | Works |
| ok | Handling `Fail` around each *total* piece inside the loop | Works, but exits 0 and prints the error to stdout |

**G1: `Fail` and `Partial` in `main`** [ran]:

```
def loop (total: Nat): {IO, Fail, Partial} Nat :=
  match IO.readLine() with
    | None => total
    | Some line =>
      let n := Text.toNatOrFail line
      loop (total + n)

def main(): {IO, Fail, Partial} () := IO.print "sum ${loop 0}"
```

`stitchwort check` accepts the file, because `loop` is fine as a
definition. `stitchwort run` refuses it:

```
[E-MAIN-TYPE] Error: `main` must have type `() -> {IO} ()`, `() -> {IO, Partial} ()`, or `() -> {IO, Fail} ()`
 11 │ def main(): {IO, Fail, Partial} () := IO.print "sum ${loop 0}"
    │                  ╰────────────────── this has type `() -> {Fail, IO, Partial} ()`
    │ Note: a pure `main: () -> ()` is allowed too; other abilities must be handled inside `main`
```

The note says "handle it inside `main`", but that's refused too (G1′):

```
def search (n: Nat): {Fail, Partial} Nat :=
  if n > 1000 then Fail.fail "gave up" else if n * n == 1764 then n else search (n + 1)

def main(): {IO, Partial} () :=
  match Fail.toResult (() => search 0) with ...
```
```
[E-PARTIAL] Error: a computation that might not finish can't run here
 8 │   match Fail.toResult (() => search 0) with
   │                              ╰───── `search` is `Partial`: it might not finish
```

So **a `{Fail, Partial}` function checks, but nothing can ever run it.** The
cause is in `crates/driver/src/run.rs` (`main_calls`) [source]. A `main`
with `Fail` is wrapped in `Std.Fail.recover`, which is a handler, and a
handler can't take a partial computation (partial.md §7.3.8). The guide
documents the gap (`08-abilities.md`: "not yet both `Fail` and `Partial`";
`syntax.md` line 667).

The workaround is to handle `Fail` around each total piece and report the
error by hand [ran]:

```
      match Fail.toResult (() => Text.toNatOrFail line) with
        | Ok n => loop (total + n)
        | Err message => IO.print "error: ${message}"
```

With input `1 2 x 4`, this prints `error: expected a whole number, got 'x'`
**on stdout, and exits with status 0**. A total `main` with `Fail` sends
the error to stderr and exits with 1.

**G2: state around a partial loop** [ran]. `runCounter` is the usual
state-passing handler from `examples/accept/io.sw`, and `echo` is
`{IO, Counter, Partial}`. `runCounter echo` gives:

```
[E-PARTIAL] Error: a partial function can't be used where a total one is expected
 25 │   let r := runCounter echo
    │ Note 1: … a row variable like `e` never stands for `Partial`, so a function taking `{… | e}` can't be given a partial one
```

This is partial.md §7.3.8 as designed. The workaround is to pass the state
as an argument, which is fine for small programs.

**G3: partial callbacks to std** [ran].
- `List.map collatzSteps [3, 7, 27]` gives the same E-PARTIAL with the same
  note.
- A recursive search that maps itself over its children,
  `def countNodes (n: Nat): {Partial} Nat := 1 + List.sum (List.map countNodes (children n))`,
  gives:

  ```
  [E-PARTIAL-CALLBACK] Error: `countNodes` can't be passed to `List.map` here
    Note 1: `List.map`'s parameter has the type `Nat -> {?1 n} ?2 n`, whose row is fixed
    Note 2: make `List.map` polymorphic in the rest of the row: give the parameter the type `Nat -> {?1 n | e} ?2 n`, and add `| e` to `List.map`'s own row too
  ```

  This message is wrong in two ways. It shows unsolved metavariables
  (`?1 n`), and it tells the user to change std's `List.map`, which is
  already row-polymorphic. The real reason is that its row variable can't
  be partial.
- `List.filter isBig xs`, with a partial `isBig`, is a plain type mismatch:
  `expected Nat -> Bool, but this has type Nat -> {Partial} Bool`. That's
  expected, because `filter` takes pure callbacks today.

The workaround is a hand-written `mapP`, as `examples/accept/partial.sw`
has. It's partial itself, so it costs a tick per element (§1.2).

**G4: testing.** `test "27 takes 111 steps" := collatzSteps 27 == 111` is
E-PARTIAL. The guide shows this (`07-recursion.md`), and its note says to
"test a total function instead, such as one that takes a step limit". So
the program carries two Collatz functions [ran, checks]:

```
def collatzFuel: Nat -> Nat -> Option Nat
  | 0, n => None
  | Succ fuel, 1 => Some 0
  | Succ fuel, n => Option.map (s => 1 + s) (collatzFuel fuel (if n % 2 == 0 then n / 2 else 3 * n + 1))

test "27 by the fuelled copy" := collatzFuel 200 27 == Some 111
```

Nothing ties `collatzFuel` to `collatzSteps`. DESIGN.md §5 rule 5 says tests
of partial programs are "runs of `main` with scripted input and a tick
limit", but that's only reachable from Rust (`Session::simulate`,
`crates/driver/src/run.rs:305`), not from a Stitchwort `test`.

**What works** [ran]. This read loop, with `match` directly on
`IO.readLine()`, checks and runs: input `1 2 zz 5` prints `total 1`,
`total 3`, `not a number: zz`, `total 8`, `bye, total 8`.

```
def repl (total: Nat): {IO, Partial} () :=
  match IO.readLine() with
    | None => IO.print "bye, total ${total}"
    | Some line =>
      match Text.toNat line with
        | None =>
          IO.print "not a number: ${line}"
          repl total
        | Some n =>
          IO.print "total ${total + n}"
          repl (total + n)
```

`examples/accept/cat.sw` and `adder.sw` still use the older style, with a
helper taking a `| e` callback. That's no longer needed. A docs fix-up could
simplify them.

**G5: small things found on the way.**
- The E-PARTIAL-CALLBACK note above: metavariables, and advice to edit std.
- A recursive *local* definition can't be partial (E-LOCAL-DEFINITION;
  `examples/reject/local-partial-recursive.sw`; documented in `syntax.md`).
  It's minor, because a top-level definition does the same job.

**The playground** runs partial programs through the same runner, with
output cap, timeout and Stop (`crates/web/src/lib.rs:1064`
`runs_partial_programs`) [source]. It shares the `main` type check, so G1
applies there too (`crates/web/src/lib.rs:1085`) [source].

### 1.2 Speed and stack

These are from `p1-perf.sw`: the first input line picks the program, the
second the size [ran]. Times are wall-clock for the whole run, including
checking (about 0.15 s); memory is peak RSS.

| Program | Native, 100k | Native, 1M | `--js`, 100k | `--js`, 1M |
|---|---|---|---|---|
| `countdown n` (partial tail loop) | 0.15 s | 0.33 s, 46 MB | 0.27 s | 0.30 s |
| `sumTo n` (partial, non-tail) | 0.19 s | 0.54 s, 448 MB | 0.31 s | 0.68 s |
| `mapP (n => n + 1)` over `1..n` | 0.21 s | 0.91 s, 665 MB | 0.34 s | 0.87 s |
| `List.map (n => n + 1)` (total, for comparison) | 0.15 s | 0.30 s, 442 MB | 0.29 s | 0.40 s |

- **Nothing overflows.** Non-tail partial recursion a million deep runs on
  both backends, as stage 4 intended.
- **Per tick, partial code costs about 3x total code natively and 2x in
  JS.** Summing the Collatz step counts for 1..100,000 (10,753,840 steps)
  takes 3.3 s native and 1.0 s with `--js` as a partial tail-recursive
  function. A total fuelled version takes 1.0 s native and 0.5 s in JS
  (`p2-total-collatz.sw`, `p3-partial-collatz-tail.sw`). That's acceptable
  for programs whose point is the loop, but it's why `mapP` over a list is
  worth avoiding (G3).

## 2. The options, one by one

For each option: what it lets you write, the risk against principles 1
("no `Partial`, no divergence") and 2 ("checking never runs effects"), the
rough size, and what others do.

### New: `Fail` in a partial `main` (runner-performed `Fail`)

- **Lets you write** G1 as written.
- **Risk.** None to the logic. The runner is outside the total core, and
  `main` stays `{Partial}`. No handler is involved: the runner performs
  `Fail.stop msg` (print `error: msg` to stderr, exit 1) exactly as it
  performs `IO.print`. `Fail.stop` returns `Empty`, so the runner never has
  to resume (`std/Fail/Fail.sw:18-19`) [source].
- **Size.** Small, about one lane: the main check, three runners
  (reference, native, JS), tests and docs.
- **Others.** In Koka, `io` is `<exn,ioc>` and `ioc` is `<div,ioc-total>`,
  so the ordinary I/O effect includes both exceptions and divergence
  ([Koka `std/core.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk)).

### 10.1 Observing a `Delay` with fuel; partial correctness

- **Lets you write** `test "27" := Partial.runFor 200 (collatzSteps 27) == Some 111`
  (G4), and statements like "if it finishes, the answer is right".
- **Risk.** High. A total function that steps a `Delay` must provably
  finish each step. partial.md §10.1 records the review's three obligations
  (a semantic model, an abstract-machine argument, normalisation on open
  terms), and none is done. It also breaks the JS erasure of §7.6, and the
  "singleton model" consistency argument no longer covers it.
- **A cheaper variant**, without the kernel: **run tests**. A test whose
  type is `{Partial} Bool` would be run by the runner with a tick limit,
  where running out is inconclusive. It would be reported as *ran*, never
  as a proof, and never usable as one. That keeps principle 2, because the
  checker still doesn't run it. But it changes DESIGN.md §7 ("a passing
  test is a proof of one specific fact"), so it needs Matt's decision
  (§5, D3). Small to medium.
- **Others.**
  - Agda's library has exactly `runFor : ℕ → Delay A ∞ → Maybe A`, but
    under `--sized-types`
    ([`Codata/Sized/Delay.agda`](https://github.com/agda/agda-stdlib/blob/master/src/Codata/Sized/Delay.agda)),
    which isn't `--safe` (partial.md §5.6).
  - Lean's `partial_fixpoint` works for "any function whose return type is
    in certain monads (e.g. `Option`)", and Lean "generates additional
    partial correctness theorems for these monadic functions"
    ([Lean reference, Recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#partial-fixpoint)).
  - F\*: "Terms with type `Dv t` have a partial correctness semantics", but
    "one cannot even state properties of `Dv` computations in
    specifications" ([F\* book, Divergence](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).

### 10.2 Promoting partial code proved to terminate to total

- **Lets you write** a partial function, then a proof that it terminates,
  and use it in total code.
- **Risk.** High, and it needs 10.1 or an inspectable description. A body
  that makes no requests but calls a looping function passes "every request
  decreases" vacuously (partial.md §10.2). Today `decreasing` already
  covers the useful cases: AoC day 4's `settleRows` is total by a measure
  (`aoc/src/Aoc/Year2025/Day04/Day04.sw:99`).
- **Size.** Large.
- **Others.** F\*: "it should be impossible to turn a `e:Dv t` into a term
  of type `Tot t`" ([F\* book](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).
  Idris's `assert_total` "marks a subexpression as always being total",
  unchecked ([Idris 2, Theorem proving](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)).
- **Verdict.** Not needed; `decreasing` is the route.

### 10.3 Equivalence of partial programs

Research-level (coinductive bisimilarity), and no program here needs it.
Interaction Trees do it in Coq with a whole framework
([Xia et al.](https://arxiv.org/abs/1906.00046)). **Verdict:** not planned.

### 10.4 Handlers over `Delay`

- **Lets you write** G2 (`runCounter` around a partial loop) and G1′
  (`Fail.toResult` around a partial search). It would also subsume stage 2.
- **Risk.** Lower than partial.md §10.4 suggests, *as long as 10.1 isn't
  built* [inferred]. A handler over a `Delay` would be a new kernel
  constant whose result is still a `Delay`. With no way for total code to
  look inside a `Delay`, the one-element model of partial.md §7.8 still
  covers it, so the logic stays consistent. The knot problem in §10.4 needs
  an observer. The real risks are in the runtime:
  - a `Handle` frame in three runners;
  - resuming a continuation more than once across ticks;
  - state-passing carriers (`runCounter`'s carrier is a function), which
    need a parameterised-handler form, not a plain fold.
- **Size.** Large: a kernel constant or two, machine frames ×3, elaborator
  translation of `handle` over partial code, and multi-shot tests. It needs
  its own design note.
- **Others.** Koka gets this from row polymorphism, because `div` is just a
  row label ([`while : (…) -> <div|e> ()`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk)).
  Interaction Trees give meaning to events "by defining their semantics as
  monadic actions" ([Xia et al.](https://arxiv.org/abs/1906.00046)).
- **Verdict.** Later, when a program needs state around a loop. Passing
  state as an argument works today.

### 10.5 Productive loops

Keep `cat` partial, as partial.md §10.5 decided. Nothing here changes that.

### 10.6 JavaScript exports of partial functions

- **Lets you write** an exported function that returns a stepper.
- **Risk.** Low for the logic. Exports would have to stop erasing `Delay`
  (partial.md §7.6).
- **Size.** Medium. The `run --js` stepper already exists
  (`crates/js/src/run.rs`); the export API and a work budget don't.
- **Verdict.** No program needs it yet.

### 10.7 Partiality polymorphism

- **Lets you write** G3: `List.map collatzSteps xs`, and a recursive
  `countNodes` mapping itself. One `List.map` serves pure, effectful and
  partial callbacks, with no `mapP`.
- **Risk.** Moderate, all in the elaborator and std; no kernel change
  [inferred]. Partial results stay `Delay`, so they stay visible (principle
  1). The trap: just adding a third `Effects` constructor (`CompIn
  (Diverging op res) a = Delay op res a`) is wrong, for two reasons.
  - `{A | e}` is `Comp (Plus A (rowOp e))` (effect-polymorphism.md §5.C),
    so it would silently drop `e`'s partiality.
  - Any row-generic law proved by cases on `e` would get a `Delay` case
    that can't be proved, because `bindD` has no computation rules.

  So partiality needs its own index. Handlers and `{A | e}` would require
  it to be "total", and only a bare `{e}` would accept "may diverge". This
  is the shape of Koka's `<div|e>`.
- **Size.** Medium to large. It needs its own design note against the
  effect-polymorphism stages (D1121).
- **Others.** Koka's `while (predicate : () -> <div|e> bool, …) : <div|e> ()`
  ([`std/core.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk)).
  Idris's totality isn't in types: total functions may "not call any
  non-total functions" ([Idris 2](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)),
  so `map` needs no variant there.

### Summary

| Option | Real program it unblocks | Risk to principles 1–2 | Size |
|---|---|---|---|
| **`Fail` in partial `main`** | G1 (parsing loops) | none | **small** |
| 10.7 partiality polymorphism | G3 (`List.map` with partial callbacks) | moderate, elaborator only | medium–large |
| 10.1 run tests (runtime-only) | G4 (testing) | low, but changes what "test" means | small–medium |
| 10.1 fuel in the kernel | G4, partial correctness | high | large |
| 10.4 handlers over `Delay` | G2, G1′ | low (logic), medium (runtime) | large |
| 10.6 JS exports | none yet | low | medium |
| 10.2, 10.3, 10.5 | none | high / research / n/a | – |

## 3. Recommended stage 2: `main: () -> {IO, Fail, Partial} ()`

### 3.1 Rules

1. `main` (and a project's `run` target) may have type `() -> {IO, Fail,
   Partial} ()`, or any sub-row of it: `{Fail, Partial}`, `{IO, Fail}` and
   so on.
2. The runner performs `Fail.stop msg` when it reaches the bottom of the
   run. Whatever was printed stays printed, `error: msg` goes to stderr, and
   the exit status is 1. This is exactly today's behaviour for a total
   `main` with `Fail` (`syntax.md` line 667).
3. Nothing else changes:
   - a handler still can't take a partial computation (G1′ stays
     E-PARTIAL);
   - tests still can't be partial;
   - `IO.simulate` of a partial `main` is still refused.

**Implementation detail (not a decision).** One path for every `main`
with `Fail`, total or partial. The runner performs `Fail.stop`, and the
`Std.Fail.recover` wrapper in `main_calls` is removed. One code path is
simpler to test, and what users see is unchanged.

### 3.2 Diagnostics

- **E-MAIN-TYPE**: the message lists `() -> {IO, Fail, Partial} ()`. The
  note keeps "other abilities must be handled inside `main`".
- No new codes.
- In the same lane, fix G5's **E-PARTIAL-CALLBACK** note for a
  library function that's already row-polymorphic. It should say "a row
  variable can't stand for `Partial`; write a partial helper (`mapP`) for
  now", and print no metavariables.

### 3.3 Tests and examples

- `examples/accept/main-fail-partial.sw`: G1's loop.
  `crates/cli/tests/run.rs` runs it natively, with `--reference` and with
  `--js`, and expects the same stdout, stderr and status on all three:
  - input `1 2` gives `sum 3`, exit 0;
  - input `1 2 x 4` gives no stdout, `error: expected a whole number, got 'x'`
    on stderr, exit 1.
- A partial `main` that prints, then fails mid-loop: the earlier output is
  kept.
- A partial loop that fails after 1,000,000 iterations, on all three
  runners. It must keep constant frames, as `countdown` does.
- The playground (`crates/web`): the same program shows the output, then
  the error, as for a total `main` with `Fail`.
- The existing `examples/accept/main-fail.sw` and `main-fail-ok.sw` give
  unchanged output (the path changes, the behaviour doesn't).
- Still refused:
  - `{IO, Fail, Partial, Log}` gives E-MAIN-TYPE (new reject example);
  - `reject/partial-handled.sw` is unchanged.
- Docs:
  - remove "not yet both `Fail` and `Partial`" from `08-abilities.md` and
    `syntax.md`;
  - change the snippet in `07-recursion.md` or `08-abilities.md` to show a
    parsing loop;
  - add an "As built" section to this note.

### 3.4 Build plan

One lane (Sonnet; judgement in three runners), branched from local `main`:
1. Driver: `main_calls` and the main type check accept `Fail` with
   `Partial`. The reference runner performs `Fail.stop`.
2. Native (`crates/rt/src/run.rs`) and JS (`crates/js/src/run.rs`)
   runners: the same operation, routed like `IO`'s through the `Map`/`Tie`
   index of stage 4c.
3. Remove the `recover` wrapper. Check the existing `Fail`-`main` snapshots
   are unchanged.
4. The tests in §3.3, the E-PARTIAL-CALLBACK note, docs.

Checks: the named tests above plus `crates/cli/tests/run.rs` and
`crates/driver/tests/partial.rs`. Expect a few hundred lines, mostly tests.

## 4. Stage 3, in outline: partial callbacks through the one `List.map`

This is not for building yet. It needs a design note and review first,
because it touches the effect-polymorphism core (D1110, D1121).

- **The goal.** `List.map collatzSteps xs` and the recursive `countNodes`
  (G3′) check, with the *same* `List.map`. Because `map` itself isn't
  partial, it adds no ticks: only the callback's recursion counts.
  Today's `mapP` costs a tick per element, and about 3x the time and 1.5x
  the memory of `List.map` at 1M elements (§1.2).
- **The likely shape.** A partiality index beside the row index, which may
  be "total" or "may diverge":
  - a bare `{e}` accepts either; `CompIn` gives `Delay` for "may diverge";
  - a function that handles `e`, or extends it (`{A | e}`), needs "total",
    and the elaborator infers that from its signature;
  - E-PARTIAL then fires only where a handler or an extension really is.

  That's Koka's `<div|e>`, kept out of handlers as partial.md §7.3.8
  requires.
- **What the note must settle:**
  - inferred versus written partiality variables;
  - what happens to the existing row laws;
  - the backends' empty-row specialisation (E) at the new index;
  - whether `List.filter`, folds and others follow `map` one at a time (as
    D1120 did).

## 5. Decisions for Matt

1. **D-a. Stage 2 is `Fail` in a partial `main`, performed by the
   runner.** Recommended: yes. The alternative is to wait for handlers over
   `Delay` (10.4), which would cover it but is several times larger.
2. **D-b. What comes after stage 2.**
   - (a) partiality polymorphism for bare row variables, design note first
     (§4): **recommended**, because it's the D1110 `List.map` story and
     real programs hit it (G3);
   - (b) run tests for partial code (10.1's cheap variant);
   - (c) handlers over `Delay` (10.4).
3. **D-c. Should a test ever run partial code?** A runtime-only "ran"
   outcome, never a proof, would change DESIGN.md §7.
   - Recommended: yes in principle, as a distinct outcome that's never
     cached as a proof. But not now: file it when a program needs to test a
     partial function.
4. **D-d. Keep 10.2 (promotion), 10.3 (equivalence) and 10.5 (productive
   loops) out.** Recommended: yes. `decreasing` covers promotion's real
   uses.

## 6. As built (stage 2, 25 October 2026, D1179)

`main` (and a project's `run` target) may be `() -> {IO, Fail, Partial} ()`
or any part of it. All three runners and the playground perform `Fail.stop`
themselves, as they perform `IO.print`: what was printed stays, `error: msg`
goes to stderr (the playground shows it below the output), and the exit
status is 1. No kernel change, and no handler around partial code.

- **Driver** (`crates/driver/src/run.rs`, `main_calls`). The call is tried
  in `{IO, Partial}` first, so a `main` without `Fail` elaborates exactly
  as before, and then in `{IO, Fail, Partial}`. The `Std.Fail.recover`
  wrapper is gone, for total and partial `main` alike (§3.1's one path).
  With it went `CallError::Prepare` and its "while preparing `main` to run"
  diagnostic (SW-435): the call names only `Std.IO` and `Std.Fail` now, so
  nothing the program declares can break it. `Main` records which row its
  term is in (`Main::row`, `stitchwort_rt::MainRow`).
- **Why the row is recorded.** `{IO}` is `Plus IO NoOp` and `{Fail, IO}` is
  `Plus Fail (Plus IO NoOp)` (abilities sort by full name). In
  `stitchwort-rt` a constructor is only its index, so `L (print t)` and
  `L (stop m)` look the same. `lower_main` therefore takes the row, and the
  runner's `perform` decodes by it. The reference evaluator and the JS
  runner tell the two apart by the constructor itself (its data type, or
  its name as the JS tag), so they need no flag.
- **`Fail` in the registry.** `Builtin::Fail` and `Builtin::FailStop`
  (`%stop`) are library built-ins, bound when `std/Fail/Fail.sw` loads. The
  runners look them up with `loaded_data`, since a `main` without `Fail`
  needn't load the file.
- **Messages.** `E-MAIN-TYPE` lists `() -> {IO, Fail, Partial} ()`, and so
  does `E-RUN-TYPE`'s note. The E-PARTIAL-CALLBACK note (G5) was fixed
  separately, before this stage.
- **Examples.** `examples/accept/main-fail-partial.sw` (G1's loop, printing
  a running total) and `main-fail-partial-deep.sw` (a failure under a
  million waiting non-tail calls, or after a million tail calls). Both are
  `(run: fails)`, so the generic every-example harnesses skip them.
- **Tests.** `crates/cli/tests/run.rs` runs both examples with native,
  `--js` and `--reference`, and expects identical stdout, stderr and exit
  status: success (`sum 3`, exit 0); failure after output (the totals so
  far, `error: expected a whole number, got 'x'`, exit 1); failure before
  any output; and both million-deep loops (no overflow on any runner;
  about 0.5 s native, 0.7 s `--js`, 1.6 s reference for `descend`). It also
  checks `main-fail.sw` and `main-fail-ok.sw` unchanged on all three, that
  `{Fail, Partial}` and `{Partial, Fail}` run, that `{IO, Fail, Partial,
  Log}` is E-MAIN-TYPE, and that `Fail.toResult` around a partial search is
  still E-PARTIAL. `crates/web` has a playground test for the same programs.
- **Deviations from §3.3.**
  - There's no `reject/` example for `{IO, Fail, Partial, Log}`: `check`
    accepts the file (E-MAIN-TYPE comes from `run`), so it's a CLI test.
  - The SW-435 test now expects a `main` with a shadowed `Text` to run.
- **The workaround** (handling `Fail` around each total piece and printing
  the error) still prints to stdout and exits 0, as §1.1 says [ran]; that's
  the program's choice, and stage 2 makes it unnecessary.
