# Tests that run partial code (D1183)

**Status:** built, 25 October 2026. Matt approved D1183, which replaced the
heavier design this note first proposed (appendix A).

## The decision

Matt: "Tests are meant to be runtime checks, like unit tests in other
languages. If it loops forever, that's just a bug and an acceptable risk."

So:
- A `test` may call partial (`{Partial}`) code, with **no new syntax or
  annotation**. The test's type is inferred.
- Results are plain pass or fail. There's no tick limit, no "passed by
  running" result and no `@[ticks n]`.
- A test that loops is a bug; whoever ran it stops it.
- **The checker, the editor (LSP) and the playground's checks never run
  tests**, so a looping test can't hang them.

This changes DESIGN.md §7 (tests are runtime checks, not proofs) and §5
rules 4 and 5. It doesn't touch the kernel: a partial test is a `Delay`,
which the kernel never steps (partial.md §7.2).

## What was built

- **Elaborator** (`Elaborator::test`, `crates/elab/src/lib.rs`). A test is
  checked as a `Bool` first, as before. If that fails with `E-PARTIAL`, it's
  checked again against `{Partial} Bool`, the elaborated
  `Effect.Delay Effect.NoOp Effect.NoRes Bool`, exactly as the body of
  `def check(): {Partial} Bool := …` is, and declared to the kernel at that
  type. A total test is unchanged, so its hash is too. The test-only note on
  `E-PARTIAL` ("a test must finish…") is gone, with the `in_test` flag that
  chose it.
- **`stitchwort test`** (`Session::run_selected`,
  `crates/driver/src/driver.rs`). A test whose type is a `Delay`
  (`Elaborator::is_partial`) is stepped to its result as `stitchwort run`
  steps a partial `main`: on the fast runtime by default
  (`stitchwort_rt::run_partial`, the same stepping loop as `run_main`, on a
  machine of its own), and with `--reference` on the reference runner
  (`Session::run_partial`, `core::step::Machine`, as `run_loop`). Each
  stretch between two ticks has its own resource budget, as in `run`.
  As with any test, one the fast runtime can't lower or finish falls back to
  the reference runner.
- **No tick limit.** `stitchwort run` has none by default
  (`Policy::default()` has `max_ticks: None`; the only limit,
  `SIMULATED_TICKS`, is for `Session::simulate` in Rust tests), so tests
  have none either.
- **Caching.** A partial test's result is cached like any test's, under its
  content hash; running out of resources is never cached.
- **Failure detail.** A failing partial test reports `evaluated to False`:
  it has no probe, since its parts can't be computed apart from the run.
- **Who runs tests.** Only `stitchwort test` and the playground's Tests tab
  (`crates/web` `test`, `test_project`), which runs in a worker that a new
  request, Stop or a 60-second timeout terminates. Checking, the language
  server and the playground's Check tab and index never run a test; the
  kernel can't step a `Delay` anyway. Tests: `checking_never_runs_a_looping_test`
  (`crates/cli/tests/test_failures.rs`), `a_looping_test_never_runs`
  (`crates/cli/tests/lsp.rs`), `partial_tests_run_only_in_the_tests_tab`
  (`crates/web/src/lib.rs`).
- **Examples and guide.** `examples/accept/partial-tests.sw` (Collatz, a
  partial helper, mutual recursion, a block); `examples/reject/partial-in-test.sw`
  is gone. Guide chapter 7's `errors/partial-call.sw` became
  `partial-test.sw`, a test that passes; chapter 9 no longer calls a test a
  proof.

Out of scope, unchanged: `Fail` and `IO` in tests; the runners' tick
off-by-one and the native/reference tick-agreement test (appendix A §1.3).

## Appendix A: the superseded design

The first version of this note (25 October 2026) proposed a written type
(`test "…": {Partial} Bool := …`), a separate "passed by running" outcome
that was never a proof, a default limit of 1,000,000 ticks with
`@[ticks n]` to raise it, an inconclusive result at the limit, and a warning
for a `{Partial}` test that ran no partial code. D1183 dropped all of that:
tests are runtime checks, so a run is all a test ever was.

Its survey of how things stood is kept below, since its repros and its
account of the runners are still accurate history. In it, "today" means
before D1183: R1 and R2 now pass. Its §2 and §3 argued for keeping a total
test's pass as evidence, which D1183 no longer asks for. **[ran]** marks
what was run with `target/release/stitchwort` built from `main` at
`bf73a646`, **[source]** what was read in the code, and **[inferred]**
reasoning that wasn't tested.

### 1. Where things stand

#### 1.1 What's refused today

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

#### 1.2 How tests run today

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

#### 1.3 The runner already has a tick limit

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

#### 1.4 How long a million ticks takes

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

### 2. What must not break

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

### 3. Prior art

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

