# Proposal: tests that run partial code

**Status:** design note, 25 October 2026. Not built, and no decisions taken.
Matt chose this as the stage after Partial stage 2 (D1180 b). It answers
gap G4 and decision 3 of [partial-stage-2.md](partial-stage-2.md), and the
cheap variant of option 10.1 there: "a separate 'ran' result, never a proof,
which changes DESIGN.md §7".

Claims are marked like this:
- **[ran]**: run for this note with `target/release/stitchwort` built from
  `main` at `bf73a646`, on an Apple M4 Pro shared with other jobs. Times are
  single runs. The scratch programs aren't committed; each is quoted in full.
  In the quoted errors, the scratch folder's long path is cut to the file
  name.
- **[source]**: read in the code.
- **[inferred]**: my reasoning, not tested.

Claims about other languages link to a page I opened for this note.

## 0. Summary

**The problem.** A test can't call a partial function (E-PARTIAL). The only
workaround is a hand-written copy with a "fuel" parameter, and nothing ties
the copy to the real function.

**The proposal, in plain words.**
- A test may say `{Partial}` in its type:

  ```
  test "27 takes 111 steps": {Partial} Bool := collatzSteps 27 == 111
  ```

- **The checker still never runs it.** The checker checks it as it checks a
  partial `def`, and stops there.
- **`stitchwort test` runs it** the way `stitchwort run` runs a partial
  `main`: one step at a time, counting ticks (one tick per recursive call),
  and it stops at a tick limit. A tick count is part of what a program means,
  so it's the same on every machine and every runtime. Wall-clock time
  plays no part.
- **Its result has its own name.** It's reported as **passed by running**,
  never as "passed". It's never a proof, and nothing can use it as one.
- **Hitting the tick limit gives no result** ("inconclusive"), as DESIGN.md
  already says for every budget. That result is never cached.
- The default limit is **1,000,000 ticks**, the limit `simulate` already
  uses for a partial `main`. A test can raise it with `@[ticks 50_000_000]`.
- Results are cached like any test's, with the ticks used stored beside
  them.
- `IO` and `Fail` stay out of tests for now (§4.6).

That changes DESIGN.md §7 ("no `Partial` in tests") and §5 rule 5. It
doesn't touch the kernel, and it keeps principles 1 and 2 (§4.7).

Decisions for Matt are in §6, the build plan in §7, and the tests that would
show it works in §8.

## 1. Where things stand

### 1.1 What's refused today

| # | Program | Result |
|---|---|---|
| R1 | A test that calls `collatzSteps 27` | **E-PARTIAL** |
| R2 | The same, through a `{Partial} Bool` helper | **E-PARTIAL** |
| R3 | `IO.simulate` of a partial `main` in a test | **E-PARTIAL** (a handler can't take a partial computation) |
| R4 | A test with a written type, `test "…": Bool := …` | **E-PARSE**: tests take no type today |
| R5 | `IO`, or an unhandled `Fail`, in a test | **E-ABILITY** |
| R6 | A partial callback to `List.all`, even inside a partial function | **E-PARTIAL** (G3 of partial-stage-2.md) |
| ok | A test that *builds* a partial closure without running it | Passes |
| ok | A hand-written fuelled copy | Passes, but can drift from the real function |

**R1** [ran]. `t1.sw`:

```
def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

test "27 takes 111 steps" := collatzSteps 27 == 111
```

```
[E-PARTIAL] Error: a computation that might not finish can't run here
   ╭─[ t1.sw:6:30 ]
   │
 6 │ test "27 takes 111 steps" := collatzSteps 27 == 111
   │                              ───────────┬──────────
   │                                         ╰──────────── `collatzSteps` is `Partial`: it might not finish
   │
   │ Note: a test must finish, so it can't run anything that might not (and a test's type can't say `Partial`); test a total function instead, such as one that takes a step limit
───╯
```

**R2** [ran]. With `def check27(): {Partial} Bool := collatzSteps 27 == 111`
and `test "via a partial helper" := check27 ()`, the error is the same, on
`check27 ()`.

**R3** [ran]. With `def main(): {IO, Partial} () := IO.print "${collatzSteps 27}"`:

```
test "simulate a partial main" := (IO.simulate [] main).fst == ["111"]
```
```
[E-PARTIAL] Error: a partial function can't be used where a total one is expected
    ╭─[ t4.sw:10:51 ]
 10 │ test "simulate a partial main" := (IO.simulate [] main).fst == ["111"]
    │                                                   ──┬─
    │                                                     ╰─── this might not finish: its type says `Partial`
    │ Note 1: a function whose type doesn't say `Partial` must finish; a row variable like `e` never stands for `Partial`, so a function taking `{… | e}` can't be given a partial one
    │ Note 2: to accept partial functions, write `Partial` in the row: `{Partial | e}`
```

Note 2 is misleading in a test: `IO.simulate` is std's, and a handler can
never take `Partial` (partial.md §7.3.8). The fix belongs with §4.8.

**R4** [ran]. `test "a test with a type" : Bool := spin 0 == 0`:

```
[E-PARSE] Error: expected `:=`, but found `:`
 3 │ test "a test with a type" : Bool := spin 0 == 0
   │                           ╰── expected `:=`, but found `:`
```

So a written type on a test is new syntax, but there's no old meaning for it
to clash with.

**R5** [ran]. `test "IO in a test" := say ()`, with `say(): {IO} Bool`, is
`E-ABILITY: this may perform IO, which isn't allowed here`.
`test "Fail in a test" := parse "3" == 3`, with `parse: Text -> {Fail} Nat`,
is the same error for `Fail`. A total test handles `Fail` with
`Fail.toResult` (guide chapter 9).

**R6** [ran]. Even inside a partial function:

```
def allShort(): {Partial} Bool := List.all (n => collatzSteps n < 200) [1, 2, 3]
```
```
[E-PARTIAL] Error: a computation that might not finish can't run here
 8 │ def allShort(): {Partial} Bool := List.all (n => collatzSteps n < 200) [1, 2, 3]
   │                                                  ╰─────────── `collatzSteps` is `Partial`: it might not finish
```

So a partial test about many inputs needs a hand-written partial loop until
stage 3 (partiality polymorphism, partial-stage-2.md §4). This proposal
doesn't depend on stage 3, and benefits from it.

**What works** [ran]:
- `test "building a partial closure is fine" := ignore (() => collatzSteps 27)`,
  with `def ignore (f: () -> {Partial} Nat): Bool := True`, passes. Building
  a partial closure is pure; only running it is partial (DESIGN.md §3).
- The fuelled copy from partial-stage-2.md G4 passes, and the second run
  takes both from the cache:

  ```
    ✓ 27 by the fuelled copy                                      ran
    ✓ the copy can drift: nothing checks it against collatzSteps  ran
  2 test(s): 2 passed, 0 failed (0 from the cache)
    ✓ 27 by the fuelled copy                                      cached
    ✓ the copy can drift: nothing checks it against collatzSteps  cached
  2 test(s): 2 passed, 0 failed (2 from the cache)
  ```

  This is the gap: both tests are about `collatzFuel`. Nothing checks that
  `collatzSteps`, the function `main` actually runs, gives the same answers.

### 1.2 How tests run today

This matters for what "a passing test is evidence" means.

- **The kernel checks the declaration.** `test "name" := e` is elaborated to
  a core definition of type `Bool`, and the kernel checks it
  (`kernel::declare_def` and `define_def` in `Elaborator::test`,
  `crates/elab/src/lib.rs:1048`) [source].
- **A runner computes the value.** `stitchwort test` uses the fast runtime
  (`crates/rt`) by default and the reference evaluator, the kernel's own,
  with `--reference` (`crates/cli/src/main.rs:772`,
  `Session::run_tests_fast` and `run_tests` in
  `crates/driver/src/driver.rs`) [source]. A test the fast runtime can't
  lower, or that runs out of resources there, falls back to the reference
  evaluator, "whose limits a test's result is reported against"
  (`TestMachine::run`) [source]. Both erase proofs and types first.
- **What's cached.** Each result goes under
  `.stitchwort/cache/tests/<version>-<fingerprint>-<modes>-<test hash>`,
  passes and failures alike. The modes include `m` for the fast runtime, so
  the two runners' results are kept apart. "Ran out of resources" is never
  cached (docs/core.md "Tests and content hashes"; `run_selected`)
  [source].

So "a passing test is a proof of one specific fact" (DESIGN.md §7) means,
precisely: the test's claim `e = True` is a statement the kernel can check by
computation, and the reference evaluator, which is the kernel's evaluator,
computes exactly that. The fast runtime gives the same answer faster, and is
differential-tested to agree (guide chapter 9, "Two runtimes"). **For a
partial test there's no such statement at all**: `collatzSteps 27` is a
`Delay`, which the kernel can't look inside (partial.md §7.2), so
`collatzSteps 27 = 111` can't even be written as a proposition. That's the
real difference this proposal has to keep visible.

### 1.3 The runner already has a tick limit

- `Policy { max_ticks }` exists in both runners: the reference runner
  (`crates/driver/src/run.rs:74`) and the fast runtime's
  (`crates/rt/src/run.rs:36`). Reaching it gives `Outcome::OutOfTicks`,
  "inconclusive, neither success nor failure" [source].
- Only one caller sets it: `Session::simulate` of a partial `main`, with
  `SIMULATED_TICKS = 1_000_000` (`run.rs:544`), from Rust tests [source].
  The fast runtime's limit has no caller and no test (grep of `crates`)
  [source].
- The JS runner has no tick limit: "JS has no tick limit"
  (`crates/js/src/run.rs:18`) [source].
- **The limit's boundary is off by one** against partial.md §7.4.3. Both
  runners stop as soon as the count *reaches* the limit (`ticks >= max`), so
  a computation that needs exactly `n` ticks is stopped under a limit of `n`
  [source]. partial.md's convention is "fuel is the number of `Later`s that
  may be crossed": `runFor 111 (collatzSteps 27)` finishes. The two runners
  agree with each other, so nothing is wrong today. A user-visible limit
  should follow partial.md (§4.4).
- **Tick counts are tested on the reference runner only.**
  `crates/driver/tests/partial.rs` (`ticks_and_results_agree_with_the_model`)
  checks the reference runner's counts against `crates/partial-model`.
  I found no test comparing the fast runtime's counts [source]. §7 adds one.

### 1.4 How long a million ticks takes

`t10.sw` sums the Collatz step counts of 1 to 12,000: 1,038,783 ticks
inside `collatzSteps` plus 12,000 in the outer loop, about 1.05 million in
all [ran]:

```
def sumSteps (n: Nat) (total: Nat): {Partial} Nat :=
  if n == 0 then total else sumSteps (n - 1) (total + collatzSteps n)

def main(): {IO, Partial} () := IO.print "${sumSteps 12000 0}"
```

| Runner | Wall time (includes about 0.15 s of checking) |
|---|---|
| `stitchwort run` (native) | 1.07 s |
| `stitchwort run --reference` | 5.14 s |
| `stitchwort run --js` | 0.38 s |

All three print `1038783`. So a test that hits the default limit costs about
a second on the default runner and about five with `--reference`. That
seems acceptable for a test that's going wrong. How fast the playground's
WebAssembly build is, I haven't measured.

## 2. What must not break

1. **A passing total test stays evidence.** Its claim stays one the kernel
   can check by computation (§1.2), and it keeps its name, "passed".
   DESIGN.md principle 7: "One meaning per word". A run result needs a
   different word.
2. **Checking never runs effects or diverges** (principle 2), and
   **no `Partial`, no divergence** (principle 1): partiality stays visible in
   types, and no total code can observe a `Delay`.
3. **Reproducible and cacheable.** The same test on the same code gives the
   same result on every machine and every runner, so its result can be
   cached by content hash.

## 3. Prior art

| System | How code that might not finish gets tested | What a pass means |
|---|---|---|
| Agda | `runFor : ℕ → Delay A ∞ → Maybe A` in the library | A proof, but only under `--sized-types`, which `--safe` refuses |
| Lean 4 | `#eval` runs compiled code, `partial def`s included; `decide` reduces in the kernel, and can't see inside a `partial def` | `#eval`: a run. `decide`: a proof. `decide +native`: a proof that trusts the compiler, through an axiom |
| Idris 2 | Golden tests: run a program, compare its output with an expected file | A run |
| F\* | `Dv` has a partial correctness semantics; `Dv` can't become `Tot` | Not found (see below) |
| QuickCheck, Hypothesis | Wall-clock timeouts | `within` counts a timeout as a failure; Hypothesis deadlines are known to be flaky |
| Koka | `div` is an ordinary effect, inferred | No distinction: there are no proofs |

**Agda.** `runFor zero d = nothing`, `runFor (suc n) (now a) = just a`,
`runFor (suc n) (later d) = runFor n (d .force)`, in a file whose options are
`{-# OPTIONS --without-K --sized-types #-}`
([`Codata/Sized/Delay.agda`](https://github.com/agda/agda-stdlib/blob/master/src/Codata/Sized/Delay.agda)).
Agda's `--safe` is incompatible with `--sized-types`, which "lacks some
checks that rule out improper, inconsistent uses of sizes"
([Safe Agda](https://agda.readthedocs.io/en/latest/language/safe-agda.html)).
Two lessons:
- `runFor` is the in-language form of a tick limit. Stitchwort keeps it out
  of the language, so it needs none of partial.md §10.1's obligations.
- Agda's convention matches partial.md §7.4.3: `n` is the number of `later`s
  that may be crossed, and seeing `now` is free only while fuel remains
  (`runFor zero (now a)` is `nothing`, one difference worth noting).
  Stitchwort's runner doesn't have this question in the same form, because
  it checks the limit only when crossing a tick [inferred].

**Lean 4.** "Functions marked `partial` are treated as opaque constants by
the kernel and are neither unfolded nor reduced", but they "may still be used
in compiled code as usual"
([Lean reference, Recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)).
"`#eval e` evaluates the expression `e` by compiling it and running the
compiled code"
([Interacting with Lean](https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/)).
`decide +kernel` "uses kernel for reduction instead of the elaborator", and
`decide +native` "uses the native code compiler (`#eval`) to evaluate the
`Decidable` instance, admitting the result via an axiom"
([Tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)).
So Lean has exactly this split: a run (`#eval`) that works on partial code,
and a proof (`decide`) that doesn't. It keeps the trusted shortcut visible as
an axiom. Stitchwort's version: a partial test is like `#eval`, never like
`decide +native`. It never becomes a proof, with or without an axiom. I
found no page saying whether `#eval` has a step or time limit, so I don't
claim one.

**Idris 2.** "By default, Idris allows all well-typed definitions, whether
total or not"
([Idris 2, Theorem proving](https://idris2.readthedocs.io/en/latest/tutorial/theorems.html)),
so non-total functions are run like any other. Its own test harness runs
programs: "each individual golden test comprises of a directory" holding
"`run` a *shell* script that runs the test" and "`expected` a file
containing the expected output of `run`"
([`Test.Golden`](https://www.idris-lang.org/Idris2/test/source/Test.Golden.html)).
I found no timeout in it. Idris 2's base library also has a delay monad,
`Control.Monad.Partial`, with `Now` and `Later`; its only way out is
`runPartial`, which needs "a proof it is actually total"
([Idris2Doc](https://idris2docs.sinyax.net/data/base/docs/Control.Monad.Partial.html)).
There's no fuelled runner there.

**F\*.** "Terms with type `Dv t` have a *partial correctness* semantics. That
is, a term `e:Dv t` may run forever, but if it terminates then the resulting
value has type `t`", and "it should be impossible to turn a `e:Dv t` into a
term of type `Tot t`"
([F\* book, Divergence](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).
I didn't find what F\* offers for running `Dv` code in tests, so I make no
claim about it.

**QuickCheck and Hypothesis: wall-clock limits.** QuickCheck's `within`
"Considers a property failed if it does not complete within the given number
of microseconds"
([`Test.QuickCheck.Property` source](https://hackage-content-origin.haskell.org/package/QuickCheck-2.15/docs/src/Test.QuickCheck.Property.html)).
Hypothesis has a per-example deadline, and an issue titled "Busy loop
randomly runs 6x slower causing flaky DeadlineExceeded errors" reports
"Test took 239.58ms, which exceeds the deadline of 100.00ms"
([hypothesis#4009](https://github.com/hypothesisworks/hypothesis/issues/4009)).
That's the case against wall time: it depends on the machine and the load,
so a result can't be cached or reproduced. Counting ticks avoids it. And
since the program might simply need more ticks, reaching the limit isn't
evidence of a bug, so it shouldn't count as a failure either (DESIGN.md §3
already says "inconclusive").

**Koka.** Divergence is an effect like any other:
`pub alias pure = <exn,div>`, "a pure function always returns the same result
when called with the same arguments but may not terminate or raise an
exception", and `pub alias ioc = <div,ioc-total>`
([`std/core.kk`](https://github.com/koka-lang/koka/blob/master/lib/std/core.kk)).
Koka has no proofs, so there's no evidence to protect, and code with `div`
is run like any code. That's the "everything is a run" end of the range.

**What to take.**
- Lean's split between a run and a proof, with a different word for each.
- Agda's counting convention: the limit is the number of ticks that may be
  crossed.
- No wall-clock limits.
- A tick limit is inconclusive, never a failure.

## 4. The design

### 4.1 Syntax: a written type on the test

```
test "27 takes 111 steps": {Partial} Bool := collatzSteps 27 == 111
```

- A test may have a type after its name: `test "name": T := e`. `T` must be
  `Bool` or `{Partial} Bool`. Anything else is a new error, E-TEST-TYPE (§4.8).
- `: Bool` is allowed, and means the same as writing no type.
- `{Partial} Bool` makes the body partial code, checked exactly as the body of
  `def check(): {Partial} Bool := …` would be. So everything that works in a
  partial function works here: `match`, blocks with `let`, calls to partial
  helpers, a decided comparison like `collatzSteps 27 < 112`. That last one
  is [inferred]: it works in a partial `def`, and the test body would be
  elaborated the same way.
- No new keyword. The colon style is the one definitions use
  (`def f(): {Partial} Bool`), and it's where the current error note already
  points ("a test's type can't say `Partial`").

**Why written, not inferred.** The alternative is to infer it: a test whose
body is partial just becomes a run test. That needs no syntax at all, but a
total test would then quietly lose its proof status when someone makes a
function it calls partial. Principle 1 asks for partiality to be visible
where it matters, and DESIGN.md §5 rule 4 says nothing may "quietly remove"
it. Writing `{Partial}` on the test is the same rule applied to tests: the
reader sees from the test alone that it's a run, not a proof.

**Why not an attribute such as `@[run]`.** attributes.md §4.4 keeps
attributes for things that don't change the checked core or typing. Making a
test partial changes its type, so it belongs in the type (attributes.md: "A
feature that changes the core or typing stays ordinary syntax or a keyword").

### 4.2 Who runs it

- **The checker** checks the test's declaration: a definition whose type is
  the elaborated `{Partial} Bool`, a `Delay` with no operations. The kernel
  never steps a `Delay` (it has no computation rules: partial.md §7.2), so
  checking can't loop, whatever the body does. That's principle 2, with no
  new code in the kernel.
- **`stitchwort test`** runs it with the same stepping loop `stitchwort run`
  uses for a partial `main`, on the same runner the test command already
  picks:
  - by default the fast runtime's loop (`crates/rt/src/run.rs`), with the
    tick limit as its `Policy`;
  - with `--reference`, the reference loop (`run_loop` in
    `crates/driver/src/run.rs`), with the same limit.

  The test has no operations, so the loop never performs anything. An
  operation reaching the bottom would be an internal error.
- **The fallback stays as it is for total tests.** If the fast runtime can't
  lower the test, or runs out of per-step resources, the test runs on the
  reference loop. Reaching the tick limit is different: the counts are the
  same on both runners (§4.4), so the reference loop would reach it too, and
  the result is reported without a second run [inferred; §7 adds the test
  that makes this safe].
- **JS doesn't run tests** today, and needn't start. `run --js` already
  counts ticks the same way (a tick is a `Recur` reaching a `Tie`,
  `crates/js/src/run.rs`) [source]. The differential test in §7 can cover it
  too, by comparing tick counts from `run --js` with a test hook.
- **The playground** runs tests through the fast runtime
  (`crates/web/src/lib.rs`, `test_answer` calls `run_tests_fast`) [source],
  so it gets the same behaviour. Its 15-second timeout and Stop button are
  on top of the tick limit.

### 4.3 Outcomes and how they're reported

A partial test has four possible outcomes:

| Outcome | When | Mark | Cached | Exit status of `stitchwort test` |
|---|---|---|---|---|
| **passed by running** | It finished within the limit, with `True` | `✓` | yes | success (but see D5) |
| **failed** | It finished within the limit, with `False` | `✗` | yes | failure |
| **no result: tick limit** | It reached the limit | `!` | **never** | failure |
| **no result: resources** | One step did too much work, as for any test | `!` | never | failure |

The output, against today's (§1.1):

```
  ✓ 27 takes 111 steps        ran     (passed by running: 111 ticks)
  ✓ fib 10                    cached  (passed by running: 176 ticks)
  ✗ 6 takes 9 steps           ran     (`==` is False, after 8 ticks)
      left:  8
      right: 9
  ! spin stops                ran     (no result: more than 1,000,000 ticks, the limit)
  ✓ reverse twice             cached
5 test(s): 1 passed, 2 passed by running, 1 failed, 1 with no result (2 from the cache)
```

- `ran` and `cached` keep their current meaning: whether this run computed
  the result. The kind of result goes in the brackets, which today hold the
  reason for a failure.
- The tick count is shown because it's deterministic, so it's stable in
  snapshots, and because it says how close the test is to its limit.
- "passed by running" is counted apart in the summary line, so "passed"
  keeps one meaning (principle 7).
- **Failures explain themselves** as total tests' do (D601): the two sides of
  a comparison, and the false operand of an `&&`. The sides of a partial
  test are partial, so each is run again by the same loop, under the same
  limit. A side that reaches the limit is shown as `…` [inferred: the probe
  terms would be `Delay`s like the test's].
- Today's summary says "ran out of resources" for no result. Both kinds of
  no result would be reported together as "with no result", with the reason
  on each test's line.

**Never a proof.** This holds by construction, not by a check that could be
forgotten [inferred]:
- the test's type is a `Delay`, so even if something could refer to a test,
  it would get a `Delay`, which no total code can look inside;
- nothing can refer to a test anyway (the elaborator admits a test's helpers
  first because "Nothing refers to the test", `lib.rs`) [source];
- the cache stores the kind of result, and a "passed by running" entry is
  never read back as "passed" (§4.5).

### 4.4 Tick limits

**What a tick is.** One recursive call of a partial function, to itself or to
a sibling in its group. Entering a partial function, finishing, and total
work cost nothing (partial.md §7.4.3). `collatzSteps 27` takes 111 ticks and
`fib 10` takes 176; the reference runner is tested against the model on
these numbers (`crates/driver/tests/partial.rs`) [source].

**Why it's deterministic.** Ticks are part of the meaning of the program, not
of the machine running it. The run module says so: "Ticks are part of what a
program means; the runner's limits aren't" (`run.rs`, module comment)
[source]. So the count doesn't depend on:
- the machine or its load;
- the runner (reference, native, JS), as long as each implements the stepping
  rules. That's an obligation partial.md §7.8 already records, and §7 here
  adds the missing test for the fast runtime;
- optimisations, as long as they keep the number of recursive calls. A
  rewrite that turned recursion into a loop would have to keep counting
  ticks [inferred].

**The rule.** A limit of `n` lets the test cross `n` ticks: a test that makes
at most `n` recursive calls finishes. This is partial.md §7.4.3's convention
and Agda's. Both runners stop one tick early today (§1.3); the build fixes
both together, and the boundary tests in §8 pin it. This is an implementation
detail, not a decision.

**The default: 1,000,000 ticks.** It's the limit `simulate` already uses
(`SIMULATED_TICKS`). It costs about a second on the default runner and about
five on `--reference` (§1.4). It's big enough for unit-sized checks (summing
the Collatz steps of 1 to 10,000, or `fib 25`), and small enough that a looping test is
noticed quickly.

**The override: `@[ticks 50_000_000]` on the test.**

```
@[ticks 50_000_000]
test "all of 1..100000": {Partial} Bool := sumSteps 100000 0 == 10753840
```

- It's an attribute because it changes no type and no meaning, only what the
  runner may do. That's the kind of thing attributes.md §4.4 allows. Bare
  names are reserved for language attributes (attributes.md §4.3), and this
  would be the first.
- It needs a **number argument**, which the attribute grammar reserves but
  doesn't have yet (attributes.md §4.1: "Other forms (identifiers, numbers,
  `key = value`) are reserved"). Adding it is compatible.
- It's allowed only on a `{Partial}` test. Elsewhere it's E-ATTRIBUTE.
- **No command-line flag.** The limit is part of the test, written beside
  it, so a result never depends on how the command was typed, and the cache
  key needs no flag. If a project ever needs a default other than 1,000,000,
  a project setting can come later.
- It's **not** part of the test's content hash, like the `js.*` attributes
  (core.md, "Tests and content hashes"). §4.5 says why that's safe.

### 4.5 Caching

- **Key.** Unchanged: compiler version, fingerprint, modes (with `m` for the
  fast runtime) and the test's hash. `{Partial}` is in the test's type, and
  the type is hashed (DESIGN.md §11), so a test that changes between total and
  partial gets a new hash and never reuses the other kind's result.
- **Value.** The kind of result and, for a partial test, the ticks it used:
  `passed by running, 111 ticks` or `failed, 8 ticks`.
- **Reuse.** A cached partial result is reused only if its ticks are within
  the test's current limit. Because ticks are deterministic, a result found
  under one limit holds under any larger one. That's why the limit needn't
  be in the hash. A limit lowered below the cached count reruns the test, and
  it then reports no result.
- **No result is never cached**, as today. Raising the limit retries.
- **Old cache entries.** The compiler fingerprint changes with the build, so
  no entry from before is ever read.

### 4.6 `IO` and `Fail`

- **`IO` stays out of tests.** A test is closed: its result mustn't depend
  on the terminal. Testing a partial `main` with scripted input (DESIGN.md §5
  rule 5) would need the runner to perform `IO` from a script, inside
  `stitchwort test`. It's the same machinery as this proposal, plus scripted
  input, and could come later when a program needs it. Until then, the
  pattern is the one partial.md recommends: keep the `IO` shell thin, and test
  the partial function it calls.
- **`Fail` stays out too, for now.** A total test handles `Fail` with
  `Fail.toResult` (R5). A partial test can't, because a handler can't take a
  partial computation (partial.md §7.3.8). Two ways round it:
  - Today, handle `Fail` around the total parts first, then run the partial
    part on the result:

    ```
    test "solves the example": {Partial} Bool :=
      let pairs := Fail.orElse [] (() => parsePairs example)
      solve pairs == 42
    ```

  - Later, after stage 2: allow `{Fail, Partial} Bool`. The runner would
    perform `Fail.stop msg` as stage 2 makes it do for `main`, and the test
    would be **failed**, with `msg` shown. That's small once stage 2 is
    built, but it's a new rule for tests (total tests don't allow a bare
    `Fail` either), so it's D6 rather than part of this stage.
- **Other abilities.** Through a handler, as today. A handler can't wrap
  partial code, so in practice a partial test is pure apart from `Partial`.

### 4.7 Why principles 1 and 2 still hold

- **Principle 2 (checking never runs effects).** The checker sees a
  definition whose type is a `Delay`. It checks the body the way it checks
  any partial definition's, and never steps it. No new kernel constant, no
  new reduction rule [source: partial.md §7.2, as built].
- **Principle 1 (no `Partial`, no divergence).** `Partial` is in the test's
  type. No total code can refer to the test, or observe its `Delay`. The
  singleton-model argument of partial.md §7.8 is untouched, because nothing
  new can look inside a `Delay`; only the runner steps it, as it already does
  for `main`. So the JS erasure of partial.md §7.6 stays valid too.
- **What changes is DESIGN.md's wording**, not its guarantees:
  - §7: "A test is a named, closed expression of type `Bool` that must be
    checked, total and pure" becomes "of type `Bool`, or `{Partial} Bool`";
    the bullet "No `Partial` in tests" is replaced by a short paragraph on
    run tests, saying they are never proofs;
  - §5 rule 5: "Tests may not use `Partial`" becomes "A test that says
    `{Partial}` is run by the test runner with a tick limit, where running out
    is inconclusive; its result is never a proof";
  - §4's tour gains one line of example output;
  - §11's cache table: the test-result value is "pass / pass by running /
    fail".

### 4.8 Diagnostics

| Code | When | Message (draft) |
|---|---|---|
| E-PARTIAL (changed note) | A test without `{Partial}` runs partial code | Note: "a test that runs partial code must say so: `test "…": {Partial} Bool := …`. It's then run with a tick limit, and its result is never a proof" |
| E-TEST-TYPE (new) | A test's type is neither `Bool` nor `{Partial} Bool` | "a test's type is `Bool` or `{Partial} Bool`". Note for `{IO, …}`: "a test can't perform IO; test the function `main` calls". Note for `{Fail, …}`: "handle `Fail` with `Fail.toResult` or `Fail.orElse`" |
| E-ATTRIBUTE (existing) | `@[ticks n]` on a total test, or anywhere else | "`ticks` applies only to a test whose type says `{Partial}`" |
| W-TEST-NOT-PARTIAL (new warning) | A `{Partial}` test runs no partial code | "this test runs no partial code: drop `{Partial}` so it counts as passed, not passed by running" |
| (test output) | Tick limit reached | "no result: more than 1,000,000 ticks, the limit; raise it with `@[ticks …]`, or check that the code finishes" |

The warning matters because the marker costs something: such a test would
be reported as "passed by running" when it could have been "passed". Warnings
exist already (`W-DECREASING-UNUSED`, `W-UNREACHABLE`) [source].

R3's misleading Note 2 (§1.1) should also be fixed: when the function being
given a partial argument is a handler, or comes from std, it shouldn't
suggest writing `{Partial | e}`.

### 4.9 Guide changes

- **Chapter 7 (recursion), "`Partial`".** Replace the fuel workaround with a
  partial test:

  ```
  test "27 takes 111 steps": {Partial} Bool := collatzSteps 27 == 111
  ```

  with its output, and one paragraph: partial tests are run, with a tick
  limit, and never count as proofs. The E-PARTIAL example stays, with the new
  note. "Tests and the type checker never do" becomes "The type checker never
  does; a test does only if its type says `{Partial}`".
- **Chapter 9 (testing).** A new section, "Testing partial code", after
  "Testing effectful code":
  - the syntax, and the four outcomes, with a `failing/` example showing a
    failure, a tick-limit result, and the summary line;
  - ticks and `@[ticks …]`;
  - why a run isn't a proof, in two sentences.

  The opening paragraph's "They can't … call `Partial` code" becomes "…
  unless they say `{Partial}`". "Tests and proofs" gains: "A test that says
  `{Partial}` isn't a proof: it shows the code gave this answer when run,
  within the tick limit."
- **syntax.md.** The `Partial` section's last bullet ("Tests can't"), the
  test entry near line 1104, and the attribute list.
- **examples.** `examples/accept/partial-tests.sw`, and the guide's
  `failing/` snippets (§8).

## 5. Alternatives considered

- **Fuel in the kernel (`runFor`).** It would make a partial test a real
  proof, but it needs partial.md §10.1's three open obligations and breaks
  the JS erasure. Out of scope (partial-stage-2.md §2).
- **Inferred partiality** (no marker). Least syntax, but silent (§4.1).
- **Wall-clock limits.** Not reproducible, so not cacheable (§3, Hypothesis).
- **Tick limit as a failure.** Simpler to explain, but contradicts DESIGN.md
  §3 ("Running out of budget is reported as **inconclusive**, never as pass or
  fail"), and would cache a "failure" that's really "needs more ticks".
- **A command-line `--ticks` flag.** Makes results depend on the command
  line, so the limit would have to go in the cache key. The attribute is
  simpler (§4.4).
- **Generalising `IO.simulate` for partial `main`.** A handler can't take
  `Partial`, so this is either handlers over `Delay` (partial.md §10.4, large)
  or runner-performed scripted `IO` in tests (§4.6, later).

## 6. Decisions for Matt

1. **D1. Should a test ever run partial code?** As a distinct outcome,
   "passed by running", never a proof and never usable as one. DESIGN.md §7
   and §5 rule 5 change as §4.7 says. **Recommended: yes.** It closes G4 with
   no kernel change, and the result's name keeps "passed" meaning what it
   does today.
2. **D2. How a test says it's partial.**
   - (a) A written type: `test "…": {Partial} Bool := …`. **Recommended.**
     Partiality stays visible, and it's the syntax definitions already use.
   - (b) Inferred from the body: no syntax, but a total test can silently
     become a run.
   - (c) An attribute or keyword (`@[run] test …`).
3. **D3. Reaching the tick limit is "no result"**: never cached, and
   `stitchwort test` exits with failure. **Recommended: yes**, as DESIGN.md
   §3 and §7 already say for every budget. The alternative is to count it as
   a failure.
4. **D4. Tick limits.** Default 1,000,000, overridden per test with
   `@[ticks n]`, the first bare-name language attribute and the first with a
   number argument; no command-line flag. **Recommended: yes.** The
   alternatives are a `ticks n` clause in the test's syntax, or a
   project-level setting only.
5. **D5. A "passed by running" test counts as a pass for the exit status**
   of `stitchwort test` (and in CI). **Recommended: yes.** It's a test that
   did what it says. It's labelled differently, but it doesn't make the
   command fail.
6. **D6. `Fail` in a partial test.** Allow `{Fail, Partial} Bool` once stage 2
   is built, with an unhandled `Fail` making the test fail with its message.
   **Recommended: not now.** The `Fail.orElse` pattern of §4.6 covers today's
   programs. Revisit when a program needs it.
7. **D7. A warning when a `{Partial}` test runs no partial code**
   (W-TEST-NOT-PARTIAL). **Recommended: yes**, so tests don't lose proof
   status by accident.

## 7. Build plan

Three lanes, each branched from local `main`. Lane 1 first, then 2 and 3 in
parallel. Each runs only the named tests for its change.

**Lane 1 (Sonnet): partial tests on the reference runner.**
1. Parser: an optional `: T` after a test's name. The attribute grammar
   takes a number argument, and `@[ticks n]` is registered for tests only.
2. Elaborator (`Elaborator::test`): `T` is `Bool` or `{Partial} Bool`
   (E-TEST-TYPE). A partial test's body is elaborated as a partial
   definition's is, and declared with the `Delay` type. `TestDecl` gains
   `partial: bool` and `ticks: Option<u64>`. The new E-PARTIAL note, and
   W-TEST-NOT-PARTIAL.
3. Driver: a partial test runs on the reference loop. `run_loop` is
   generalised from `Main` to any closed `Delay` with a row, with
   `Policy { max_ticks }` and the §4.4 boundary (`ticks > max` when crossing).
   `simulate`'s limit moves to the same rule.
   On the default runner, a partial test falls back to the reference loop
   until lane 2.
4. `Outcome` gains `PassedByRunning { ticks }`, and `Failed` and the
   tick-limit result carry ticks for partial tests. Cache values store them,
   with the reuse rule of §4.5.
5. CLI output and the summary line (§4.3). Failure probes for partial sides.
6. Tests: §8 items 1-6 and 9, on `--reference`.

**Lane 2 (Sonnet): the fast runtime, and agreement.**
1. Lower a partial test for the fast runtime and run it with its
   `run_main_with`-style loop and the tick limit, with the same boundary fix.
2. A differential test: on every program in `crates/driver/tests/partial.rs`
   (and the partial examples), the fast runtime's tick counts and outcomes
   equal the reference runner's. Add `run --js` counts if a hook is cheap.
3. Playground: partial tests show "passed by running" in the test panel.
4. Tests: §8 items 7 and 8.

**Lane 3 (DeepSeek, mechanical, with an exact file list): docs.**
Guide chapters 7 and 9, syntax.md, DESIGN.md §4, §5 rule 5, §7 and §11,
with snippet outputs regenerated; R3's misleading note. An "As built" section
here. Lane 3 can start once lane 1 has merged, because the outputs come from
the real binary.

Size [inferred]: lane 1 is a few hundred lines plus tests; lane 2 is smaller.

## 8. What would show it works

1. **The motivating test passes by running.**
   `examples/accept/partial-tests.sw`:
   `test "27 takes 111 steps": {Partial} Bool := collatzSteps 27 == 111`
   reports `passed by running: 111 ticks`. `fib 10` reports 176, mutual
   `isEven 10` reports 10, and a partial function that doesn't recurse
   reports 0. These numbers come from partial.md §7.4.3's table, so they also
   check that the test loop counts as `run` does.
2. **The boundary.** With `@[ticks 111]`, the Collatz test passes. With
   `@[ticks 110]`, it gives no result.
3. **Failure shows the sides.** `collatzSteps 6 == 9` fails, showing
   `left: 8` and `right: 9`. An `&&` of a true and a false partial comparison
   names the false one.
4. **A loop gives no result, quickly.**
   `test "spin": {Partial} Bool := spin 0 == 0` reports no result at the
   default limit, and is never cached: the next run runs it again.
5. **Checking doesn't run it.** `stitchwort check` on the `spin` test returns
   at once (principle 2). This is the test that would hang if the checker
   ever stepped a `Delay`.
6. **Caching.** A second `stitchwort test` shows `cached (passed by running:
   111 ticks)`. Lowering the limit below 111 reruns it, and it gives no
   result. Changing `collatzSteps` reruns it. A total test and a partial test
   with the same body don't share a cache entry.
7. **The runners agree.** `stitchwort test` and `stitchwort test --reference`
   give the same outcomes and the same tick counts on
   `examples/accept/partial-tests.sw` and on the `failing/` examples.
8. **The playground** shows the partial test as passed by running.
9. **Still refused**, as new `examples/reject/` files with their codes:
   - R1 without the marker: E-PARTIAL, with the new note;
   - `test "…": {IO, Partial} Bool := …`: E-TEST-TYPE;
   - `test "…": Nat := 3`: E-TEST-TYPE;
   - `@[ticks 5]` on a total test: E-ATTRIBUTE;
   - `@[ticks "5"]`: E-ATTRIBUTE (a string where a number is wanted);
   - a `{Partial}` test with a total body: checks, with W-TEST-NOT-PARTIAL.

## What I couldn't verify

- Whether Lean's `#eval` has a step or time limit, and what F\* offers for
  running `Dv` code in tests. I found no page saying either, so I make no
  claim.
- That the fast runtime counts ticks exactly as the reference runner does.
  It's designed to, and `run` outputs agree, but no test compares the counts
  (§1.3). Lane 2 adds that test before anything relies on it.
- The playground's speed per tick.
- That a decided proposition (`collatzSteps 27 < 112`) elaborates in a
  partial test body as in a partial `def` [inferred].
