# Where `stitchwort run` spends its time

**Status:** measurements and recommendations, 19 October 2026. Docs only: nothing here
changes the compiler. The counters and experiments below were scratch changes, measured and
then thrown away.

## The short version

- `aoc/src/day04/day04.sw` on the real input takes **16.4 s** (Apple M4 Pro, release build). That is
  **687 million machine steps** at about **42 million steps a second**, and about **410 CPU
  instructions per step** (282 billion instructions retired, from `/usr/bin/time -l`).
- The cost per step is the main problem, more than the number of steps. Most of a step goes on
  **allocating and freeing memory**: building and growing argument lists, copying
  environments, and freeing values. The system allocator alone takes about **25% of the time**,
  and Rust code that builds and frees values takes another 30% or so.
- The number of steps is also higher than it needs to be, for three reasons the language
  creates:
  1. **Arguments arrive one at a time.** `List.zipWith f xs ys` has 6 parameters (3 of them
     erased types), and each recursive call goes through 5 half-applied stages before it runs.
     On day 4 that's **79.7 million half-applied stages** against **19 million real calls**.
  2. **`if` is a function call with two closures.** `if c then a else b` is
     `Bool.ifThenElse c (\_ => a) (\_ => b)`: 3.2 million of them on day 4, 3 per comparison
     in a sort.
  3. **`==` on numbers goes through a proof-producing decision** (`Nat.decEq`, then
     `Decidable.toBool`) instead of the native `Nat.equal`.
- **The extracted JavaScript is 14 to 30 times faster today** (day 4 in 0.55 s; a sort of
  100,000 numbers in 0.41 s instead of 5.9 s), with no compiler change, by exporting a solver
  function and calling it from a five-line Node script. It needs a large stack for long lists.
- Recommendation: run AoC programs through JS now (driver script; later a proper
  `run --js`), take the two measured quick wins (native lookup, allocator), and leave the deep
  work on the reference evaluator for later. That evaluator is also the type checker's, so
  every change to it touches the trusted core.

## 1. How a program runs today, in brief

`stitchwort run` (`crates/cli/src/main.rs` `run_main`) checks the file, then
`Session::run_main` (`crates/driver/src/run.rs`) evaluates `main` with the **same machine the
type checker uses** (`crates/core/src/value.rs`, function `run`). Effects are data: `main`
evaluates to a `Comp` value, and the driver loop performs each `IO` operation and feeds the
reply back (`crates/core/src/step.rs`). That machinery is cheap here: day 4 does one
`readAll` and two `print`s, and the whole computation happens inside one reply.

While running, **erasure** is on (`crates/core/src/erase.rs`): proofs and types are replaced
by a placeholder and not computed. They are still *passed*, though: an erased type argument is
an extra argument in every call.

The machine is a loop over states (evaluate a term, apply a function, unfold a definition,
walk a case tree, return a value) with an explicit stack of pending work, so deep recursion
doesn't use the Rust stack and calls in tail position don't grow the stack. Each loop turn is
one "step" (`Budget::step`).

**Numbers** are `Value::Nat(Rc<BigUint>)`: an arbitrary-precision integer behind a shared
pointer, not a chain of `Succ`. `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.leq`, `Nat.equal`,
`Nat.divFuel`, `Nat.decEq` and two proof helpers are **native** (`crates/core/src/native.rs`):
when a definition has all its arguments, the machine looks its id up in a hash map of natives.
Everything else, including `List.zipWith`, `List.foldLeft`, `List.sum`, `List.sumBy` and the sort,
is ordinary prelude code (`crates/elab/src/prelude.sw`) run by the machine.

## 2. What was measured

Tools: release build (`cargo build --release -p stitchwort-cli`), `samply` 0.13.1 (run with
`nix shell nixpkgs#samply`, not added to the flake) on a copy built with line tables,
and scratch counters added to `value.rs` (steps by kind; calls per definition, split into
real calls, native calls and half-applied stages). Times are `user` seconds from
`/usr/bin/time`, single runs, quiet machine.

### Day 4

| | |
|---|---|
| Wall time | 16.4 s (part 2: 84 rounds of `Grid.round`) |
| Machine steps | 687 million (42 million a second) |
| Instructions | 282 billion (about 410 per step) |
| Peak memory | 233 MB |

Calls per definition while running (scratch counters):

| Definition (parameters) | real calls | native calls | half-applied stages |
|---|---:|---:|---:|
| `List.zipWith` (6) | 7,953,535 | | 39,629,975 |
| `Nat.add` (2) | | 9,511,976 | 9,511,976 |
| `List.foldLeft` (5) | 3,247,037 | | 12,988,148 |
| `Bool.ifThenElse` (4) | 3,163,178 | | 9,489,534 |
| `List.append` (3) | 1,583,738 | | 3,167,476 |
| `Decidable.toBool` (2) | 1,939,907 | | 1,939,907 |
| `Nat.decEq` (2) | | 1,572,244 | 1,572,244 |
| `Effect.runPure` (2) | 11,729 | | 11,729 |

Totals: 110 million "unfold" steps, of which **79.7 million only added one argument to a
half-applied definition**; the argument lists handled at those steps held 300 million values
in all (they're rebuilt and grown one element at a time). 181 million frames were pushed. Of
the effect machinery only `Effect.runPure` shows up (a `let` block is elaborated into
`Effect.runPure (Done …)`), and only 11,729 times: **effects in pure code cost nothing worth
measuring here**.

Profile (samply, 16,746 samples). Time **inside** each function and what it calls (the
percentages overlap):

| % | Function | What it is |
|---:|---|---|
| 99 | `value::run` | the machine loop (33% of all time is in its own body, after inlining) |
| 14.2 | `Values::drop` | freeing constructor fields and environments (stack-safe work list) |
| 9.3 | `apply_step` | applying a function, or adding an argument to a half-applied definition |
| 8.8 | `RawVecInner::finish_grow` | growing a `Vec`: argument lists and environments |
| 8.6 | `try_process` / `Vec::from_iter` | collecting a definition's arguments into a fresh `Vec` (`unfold`, `native::run`) |
| 8.4 | `fields` | building constructor values (`Cons`) |
| 7.0 | `branch` | case trees: copying the matched fields into the environment |
| 5.1 | `native::run` | natives, including copying each `BigUint` argument |
| 4.5 | `hash_one` + `write_usize` | looking up natives in a `HashMap` with the default (SipHash) hasher, on every unfold |
| 3.9 | `Value::clone` | copying values, e.g. a half-applied function taken from the environment copies its argument list |
| 2.3 | `Rc::from_iter_exact` (in `enter`) | copying a closure's whole environment on every call of a lambda |

Time by library (where the processor actually was): **stitchwort 75%, the system allocator
(`libsystem_malloc`) 15.8%, `libsystem_platform` (memset, memmove) 6.5%, the kernel 2.6%**
(called from `malloc`). So about a quarter of the time is the allocator itself.

### Micro-benchmarks

Each program reads `n` from standard input and prints one number, so the checker can't
compute it ahead of time (see section 6). `n = 100,000`; times are after subtracting the
0.11 s it takes to start and check the prelude; steps per element are from the counters.

| Program | Time per element | Steps per element |
|---|---:|---:|
| `countDown n 0` (a tail-recursive loop on `Nat`) | 0.3 µs | 10 |
| `List.length (List.range n)` | 0.8 µs | 29 |
| `List.sum (List.range n)` | 1.2 µs | 52 |
| `List.foldLeft (\acc x => acc + x) 0 (List.range n)` | 1.5 µs | 62 |
| `List.sum (List.map (\x => x + 1) (List.range n))` | 2.2 µs | 93 |
| `List.count (\x => x == 50000) (List.range n)` | 2.5 µs | 96 |
| `List.sum (List.zipWith Nat.add (List.range n) (List.range n))` | 2.8 µs | 118 |
| `List.count (\x => x <= 50000) (List.range n)` | 2.9 µs | 113 |
| `List.sum (List.map (\x => if x == 7 then 1 else 0) (List.range n))` | 3.1 µs | 123 |
| `List.sortBy Nat.compare` of `n` numbers | **3.8 µs per comparison** (5.9 s in all) | 156 per comparison |

The sort made 1.56 million comparisons, each costing **3 `if`s** (one in `List.merge`, two in
`Nat.compare`): 4.6 million `Bool.ifThenElse` calls with 13.9 million half-applied stages.

**Day 8 estimate, revised (a guess):** sorting 500,000 items by merge sort is about 8.8 million
comparisons. At 3.8 µs each that's about **33 s for number keys alone**; pairs, or a
comparison built from `Ordering.andThen`, cost more. So 30 to 60 s seems likelier than the
earlier 15 to 25 s.

## 3. The top costs, ranked

1. **Memory traffic on every step** (allocator 25%; freeing 14%; growing vectors 9%; argument
   copying 9%). Almost every step allocates: a new argument list when a definition unfolds
   (`unfold` clones every argument into a fresh `Vec`), a bigger argument list when one more
   argument arrives, a fresh environment array for every lambda call (`enter` copies the
   whole captured environment plus the new argument), a `Vec` for each case tree's
   environment (`branch`), two allocations per number result (`Rc` plus the `BigUint`'s
   digits) and a `BigUint` copy per native argument. Freeing goes through a thread-local work
   list even for small values (that's what keeps freeing a million-element list from
   overflowing the stack, but it costs on every free).
2. **Half-applied stages** (79.7 million on day 4, against 30.5 million real and native calls).
   The elaborated program applies arguments one at a time, `f a b c` being `((f a) b) c`, and
   the machine only runs a definition once it has *all* its parameters, including erased
   type parameters. So a call of a 6-parameter function makes 5 intermediate values, each
   with a longer copy of the argument list. A half-applied function stored in a variable
   (like `f` inside `List.zipWith f`) is copied, argument list and all, each time it's used.
3. **Indirect forms for `if` and `==`**: each `if` builds two closures, calls
   `Bool.ifThenElse` through 3 half-applied stages, then calls one closure (copying its
   environment). Each `==` on numbers calls the native `Nat.decEq`, which builds a
   `Decidable` value (for unequal numbers, a refutation term holding two fresh copies of the
   numbers, although it's erased in effect), then `Decidable.toBool` takes it apart again.

Smaller costs: the native lookup's hashing (4.5%); `erase::of_def` on every unfold (a
`RefCell` borrow and `Rc` clone, 0.6%).

**Not significant** (checked): the effect machinery in pure code (above); proofs, which are
erased while running; Rust stack use and tail calls (the machine has its own stack, and a call
in tail position pushes nothing); the per-step budget check (one comparison); link-time
optimisation (below).

## 4. Speed-ups

### Quick wins

| | Change | Gain | Size | Risk | Who |
|---|---|---|---|---|---|
| Q1 | Look natives up by index (a `Vec` by `DefId`, or a flag on the definition) instead of a SipHash `HashMap` | **measured 3–4%** on day 4 (prototype: 16.95 s to 16.35 s user) | small | low | Sonnet |
| Q2 | Use `mimalloc` as the CLI's allocator (`#[global_allocator]` in `crates/cli`; WebAssembly unaffected) | **measured 7%** on day 4 (16.4 s to 15.2 s), 7–15% on the micro-benchmarks | small | low (one more dependency, built from C) | Sonnet |
| Q3 | Drive AoC solvers through extracted JS (export the solver, five-line Node script, large stack): no compiler change | **measured 14–30×** (section 5) | small | low (needs Node; non-`Partial` solvers only) | Sonnet |
| — | Link-time optimisation, one codegen unit | measured about 1%: not worth it | — | — | — |

### Larger changes, ranked by expected gain for the work

All gains below are **guesses** from the counters and profile, not measurements.

| | Change | Expected gain | Size | Risk | Who |
|---|---|---|---|---|---|
| 1 | **`stitchwort run --js`**: generate JS for `main` and run it under Node, with a small driver that performs `IO` operations and loops for `Partial` (section 5) | 14–30× (anchored by the measurements in section 5) | medium | medium: `Partial` isn't extractable today (`E-JS-PARTIAL`); deep recursion needs a big stack; results come from the extractor, not the trusted evaluator (it is differential-tested against it) | Opus to design, Sonnet to build |
| 2 | **Saturated calls at run time**: when a term applies a known definition to all its parameters, call it directly with all the arguments at once, and drop erased parameters altogether while running | 1.3–1.6× (removes most of the 79.7 million half-applied stages and the vector growth that goes with them) | medium | medium: the machine is shared with the checker, so this must only apply while erasure is on, and keep the checker's folding behaviour | Opus |
| 3 | **`if` without closures at run time**: evaluate `Bool.ifThenElse c (\_ => a) (\_ => b)` as a case on `c` directly | 5–10% on day 4, 15–25% on sorting (3 `if`s per comparison) | small–medium | low–medium | Sonnet, Opus review |
| 4 | **Cheaper freeing**: in `Values::drop`, skip the work list when no field is itself a uniquely owned compound value (most list cells hold a number) | 5–8% (freeing is 14%) | small–medium | medium: must stay stack-safe for million-element lists (tests exist) | Opus |
| 5 | **Move, don't copy, a definition's arguments**: `unfold` clones the whole argument list into a new `Vec` to walk the case tree; take them from the owned list instead | 5–8% (collecting is 8.6%) | small | low | Sonnet |
| 6 | **`==` on `Nat` straight to `Nat.equal`** where only a `Bool` is needed (elaborator), or a native for `Decidable.toBool (Nat.decEq m n)` | 3–5% on day 4; more where `==` is in the inner loop | small–medium | low–medium (the elaborator's choice of `==` instance) | Sonnet, Opus review |
| 7 | **Small numbers inline**: a `Value` case for numbers that fit in 64 bits, falling back to `BigUint` | 3–10%, more for arithmetic-heavy code | medium–large (every match on `Value::Nat`) | medium (natives and number views are trusted code) | Opus |
| 8 | **Environments without copying**: share the captured environment instead of copying it on each lambda call and each case branch | 3–5% on day 4 (environments are short there), much more for deeply nested lambdas | medium | medium | Opus |
| 9 | **A separate run-time evaluator** over erased terms, compiled once into closures or a simple bytecode with direct calls, numbered variables, small numbers and no per-step budget work | 10–30× (similar to the JS measurements) | large | medium: a second evaluator to keep in agreement, by differential tests like the JS backend's | Opus |

Items 2 to 8 together might give 2 to 3 times (a guess: their savings overlap). That's well
short of what the JS route gives today, which is why the recommendation is JS first.

## 5. The JS route

**Built:** `stitchwort run --js file.sw` (19 October 2026). It checks the file as `run` does,
compiles `main ()` and everything it uses to JavaScript, and runs it with Node in a worker
thread with a 2 GB stack, with a JS copy of the runner's loop and of the `Partial` stepping
machine (`crates/js/src/run.rs`; contract and differences in
[text-and-io.md, As built](proposals/text-and-io.md#as-built)). All five AoC days, wall time
including the check (Apple M4 Pro, release build, Node 22):

| Day | `check` alone | `run` | `run --js` |
|---|---:|---:|---:|
| 1 | 0.90 s | 1.04 s | 1.00 s |
| 2 | 0.80 s | 0.83 s | 0.93 s |
| 3 | 0.20 s | 0.58 s | 0.32 s |
| 4 | 0.22 s | 17.09 s | 0.96 s |
| 5 | 0.20 s | 0.92 s | 0.33 s |

Days 1 and 2 are almost all checking, so `--js` (which adds about 0.1 s for Node to start)
doesn't help them. The rest of this section is the measurement that motivated it.

Measured, with the existing `stitchwort build --js` and Node 22 from the dev shell:

| Program | `stitchwort run` | Extracted JS under Node | Ratio |
|---|---:|---:|---:|
| Day 4, both parts | 16.4 s | 0.55 s | 30× |
| Sort of 100,000 numbers (`List.sortBy Nat.compare`) | 5.9 s | 0.41 s | 14× |
| `zipWith` of two 100,000-element lists, summed | 0.28 s | 0.055 s | 5× |

(JS times are measured inside the script, so they leave out Node's start-up, about 0.1 s.)

How it was run, all in scratch: add to a copy of the program

```
export def part1 (input : Text) : Nat := Pair.fst (solve (Grid.parse input.lines))
export def part2 (input : Text) : Nat := Pair.snd (solve (Grid.parse input.lines))
```

then `stitchwort build --js d4.sw -o out`, and call `part1(readFileSync(path, "utf8"))` from
a short `.mjs` script. The generated code is plain: curried functions, objects for
constructors, `bigint` for numbers, erased type arguments left out. V8 runs it well anyway.

**The stack:** the generated code recurses on the JS stack (a loop only for tail calls), so
non-tail recursion over a long list overflows Node's default stack: the 100,000-element sort
and `zipWith` threw `StitchwortResourceError`. With `ulimit -s 65520` and
`node --stack-size=60000` both ran. (A larger `--stack-size` than the operating system's stack
crashes Node outright, exit 139.) Day 8's 500,000-element lists would need the same, or a
Worker thread with `resourceLimits.stackSizeMb`.

**What running `main` itself through JS would take** (item 1 above; all done as described,
except that the stack comes from a worker thread rather than `--stack-size`):

1. **Partial:** an export can't mention `Partial` (`E-JS-PARTIAL`), and AoC `main`s are
   `{IO, Partial}`. JS needs no tick limit; a `Partial` loop can simply loop, but the
   extractor's rule and its reasons (docs/proposals/partial.md) need revisiting.
2. **IO bindings:** `main` evaluates to a `Comp` value (`Done x`, or `Call op k`). A small JS
   driver does what `run_loop` does in Rust: on `Call`, perform the operation (`print` writes a
   line, `readLine` and `readAll` read standard input synchronously), apply `k` to the reply,
   repeat. This mirrors `IO.simulate` in the prelude, so the data shapes are already known.
3. **CLI:** `stitchwort run --js file.sw` writes the module to a temporary directory and starts
   `node` with a large stack (Node is in the dev shell, not necessarily on users' machines).
4. **Tests:** run the `aoc/` programs and `examples/` `main`s both ways and compare output,
   like the existing differential tests for exports.

Until then, Q3 (an exported solver and a driver script) works today for any day whose solver
isn't `Partial`.

## 6. A side finding: `print`'s argument is computed while checking

Checking a `main` whose `print` argument doesn't depend on input computes it at check time:
`stitchwort check` of `print (Nat.toText (List.length (List.range 200000)))` takes 0.43 s
against 0.11 s for an empty program, and the counters show the list built and measured twice
by the checker plus once by `run`. The profile of `check` puts **84% of its time under
`effects::make_call`**, which evaluates the operation's argument (`cx.eval(&x)`, in
`crates/elab/src/effects.rs`) to compute the operation's result type. `IO`'s result types
don't depend on the argument, so it could evaluate only when they do. This doesn't affect
day 4 (its prints depend on the input), but it makes closed benchmark programs look 3 times
slower, and it may be related (a guess, unconfirmed) to the known issue "`long n == long n`
gives `E-RESOURCE` at 100,000 characters".

## 7. Reproducing

- Profile: build with `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`, then
  `nix shell nixpkgs#samply -c samply record --save-only --unstable-presymbolicate -o p.json.gz
  -- ../target/release/stitchwort run Aoc.Day04.main < inputs/day04.txt` from `aoc/`, and open it with
  `samply load p.json.gz`.
- Counters: a scratch patch adding thread-local counts to `value::run`, `enter`, `unfold` and
  `branch`, printed by `run_main` when an environment variable is set. Not committed; easy to
  redo from the descriptions above.
- Micro-benchmarks: a program `def bench (n : Nat) : Nat := …` with
  `def main () : {IO} () := print (Nat.toText (bench (Maybe.withDefault 0 (Text.toNat
  (Text.trim (readAll ()))))))`, run as `echo 100000 | stitchwort run bench.sw`.
- `bench/baseline.toml` (`stitchwort-bench`) remains the regression check for any change made
  from this list.
