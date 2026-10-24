# Proposal: a fast runtime for running programs

**Status:** draft 1, 21 October 2026. Research and recommendation only: nothing here changes the
compiler. The measurements were made with scratch programs, then thrown away. Decisions are at
the [end](#decisions).

**The question (Matt):** "It might be interesting to explore a fast native evaluator: what
strategies are there, can we make use of some other library/project to run our code fast?"

## The short version

- Today `stitchwort run` uses the type checker's own evaluator (`crates/core/src/value.rs`).
  It has to stay simple and trusted, because it checks proofs. For *running* programs, speed
  matters more, and a separate runtime can't make a false proof check: like the JS backend, it
  can only get a program's output wrong, which differential tests can catch.
- `stitchwort run --js` already runs programs under Node (V8) and is **9–20× faster** than `run`
  on compute-heavy programs today. Its costs are that it needs Node installed, and it can't be
  used in the playground in the same form (browsers don't let a page choose a big stack).
- **Recommendation:** build a second evaluator in Rust, used only for running programs: the
  program is first lowered to a simpler form with the types and proofs gone (an *erased IR*),
  and then run by a small **bytecode machine with its own stack**. The same Rust code runs in the
  CLI and, compiled to WebAssembly, in the playground. A scratch prototype of the core idea ran a
  100,000-element merge sort **about 12× faster than `run`, at about the speed of Node**
  ([measurements](#3-what-was-measured)). Effort: about 8–11 lane-days in four stages.
- **Not recommended now:** embedding a JS engine (QuickJS is 8× slower than Node here and runs
  out of stack early; V8 adds tens of megabytes and a hard build), or generating native code
  (Cranelift, LLVM, C, Chez Scheme). Native code could come later from the same erased IR if
  programs need another 2–5×.
- **Meanwhile:** keep `run` on the reference evaluator by default and use `run --js` for heavy
  programs (D385).

## 1. Where the time goes today

From [evaluator-speed.md](../evaluator-speed.md) (19 October; read that for detail):

1. **Every step allocates.** Argument lists are rebuilt and grown, environments copied,
   numbers boxed twice. About a quarter of the time was the system allocator.
2. **Arguments arrive one at a time.** `f a b c` is `((f a) b) c`, and the machine only runs a
   definition once it has all its parameters, *including erased type parameters*. On day 4
   that was 79.7 million half-applied stages against 19 million real calls.
3. **`if` is a call with two closures**, and **`==` on numbers builds a proof** (`Nat.decEq`)
   that is then thrown away.
4. Each step costs about 410 machine instructions.

Since then, the day 4 time has fallen from 16.4 s to 5.3 s (today's build, below), so the
reference evaluator is getting faster; but it is still 9–20× behind the JS route on
compute-heavy code, and the remaining costs are structural: they come from evaluating the
type checker's terms directly. The type checker needs those terms (with types, proofs and
one-argument-at-a-time application) and needs an evaluator it can trust, so the fix that
helps most is not to make that evaluator cleverer but to run programs on something else.

**What the type checker's evaluator must keep doing, and a runtime need not:** produce values
that can be compared and printed back as terms (neutral terms, stuck computations), handle
open terms with free variables, count steps for the checker's budget, keep proofs and types
around. A runtime only ever runs a closed, fully checked, erased `main`.

## 2. Strategies

This section explains the main techniques, what they'd buy here, and how established
implementations use them. Expected gains are estimates unless marked measured.

### 2.1 An erased, lowered program (the IR)

Every fast option below starts from the same thing: a simpler program representation built
once, after checking, before running.

- **Erasure.** Types and proofs are removed entirely, not replaced by placeholders that are
  still passed (today an erased type argument is still an extra argument in every call). The
  JS backend already does this (`crates/js/`).
- **Known calls with all their arguments ("saturated calls").** When the code calls a known
  definition with all its runtime arguments, it becomes one direct call with an argument
  array. Only genuinely unknown calls (calling a function value, like `f` inside `List.map f`)
  go through a general "apply" that handles too few or too many arguments. This is the
  *eval/apply* scheme GHC adopted after measuring it against the alternative
  ([Marlow & Peyton Jones 2004](https://www.microsoft.com/en-us/research/publication/make-fast-curry-pushenter-vs-evalapply/)).
  It removes most of the 79.7 million half-applied stages.
- **Closure conversion and lambda lifting.** Each lambda becomes a code pointer plus a small
  array holding only the variables it actually uses (a *flat closure*), instead of a copy of
  the whole environment.
- **Variables by slot number.** Each variable is an index into the current frame, decided at
  compile time.
- **`if` and `==` specialised.** `Bool.ifThenElse c (_ => a) (_ => b)` becomes a two-way
  branch with no closures; `Decidable.toBool (Nat.decEq m n)` becomes the native `Nat.equal`.
  More generally, *case of known constructor*: a `match` on something whose constructor is
  known at compile time is resolved at compile time.
- **Natives by index**, not by hashing an id on every call.

This IR could be shared with the JS backend, which does some of these steps already in its
own way. Everything after it (bytecode, native code) is a choice of how to run the IR.

### 2.2 How to run the IR

**(a) Compile to closures.** Each IR node becomes a Rust closure that, when called, computes
that node, calling the closures of its children. There's no instruction decoding at run time;
it's simple to write (a few hundred lines), and it's often several times faster than walking
a tree. The scratch prototype in §3 is this. Its weakness here: every Stitchwort call nests
several Rust calls, so deep recursion (a non-tail recursion over a 500,000-element list) needs
a very large Rust stack. Natively that's possible (a thread with a 4 GB stack, as the
prototype did, or the [`stacker`](https://crates.io/crates/stacker) crate), but **in the
playground it isn't**: in WebAssembly in the browser, the stitchwort code may use only a small
stack (the checker's guard is 128 KiB, and V8 crashed from about 640 KiB;
[stack-safe-evaluation.md](stack-safe-evaluation.md#progress)). Making closures stack-safe
means continuation-passing or trampolines, which gives up most of their simplicity.

**(b) A bytecode machine with its own stack.** The IR is compiled to a compact list of
instructions (push a local, call definition 17 with 3 arguments, switch on the constructor
tag, build `Cons`, return …) and a loop executes them, keeping frames in a Rust `Vec`. Deep
recursion then costs heap memory, not Rust stack, in the CLI and the browser alike, and the
existing resource limits (frames, memory) are easy to check at calls. Tail calls reuse the
frame. This is how OCaml's bytecode works (the *ZINC* machine,
[Leroy 1990](https://xavierleroy.org/publi/ZINC.pdf)), and Lua's (a register machine,
[Ierusalimschy et al. 2005](https://www.lua.org/doc/jucs05.pdf)). A well-written interpreter of
this kind is usually within 1–2× of closure compilation, and both are far from the 410
instructions per step of today.

Variants: a *stack* machine (instructions push and pop, simplest to generate) or a *register*
machine (instructions name frame slots: fewer instructions, a little more work in the
compiler). The [STG machine](https://www.microsoft.com/en-us/research/?p=149862)
(GHC) is built for laziness, which Stitchwort doesn't need.

**(c) Native code** (Cranelift, LLVM, C, or another language's compiler; §2.6). Another 2–5×
over a good interpreter on typical functional code, at a much higher cost, and none of it
runs in the playground except WebAssembly generated as output.

### 2.3 Numbers

Today every number is `Rc<BigUint>`: two allocations per result. The usual answer, used by
Lean 4, OCaml's Zarith and most Schemes, is **small numbers inline**: a value is either a
machine integer (63 or 64 bits) or a pointer to a bignum, and arithmetic checks for overflow
(one CPU flag test) and falls back to the bignum only then. AoC numbers almost always fit.
Expected: allocation-free arithmetic in the common case; on the arithmetic-heavy day 2 brute
force, probably the biggest single gain after the IR.

### 2.4 Memory: reference counting with reuse

Rust programs usually manage such values with `Rc` (reference counting), as the reference
evaluator does. Two refinements from the functional-language literature:

- **Reuse in place** (Lean 4's *reset/reuse*,
  [Ullrich & de Moura 2019, "Counting Immutable Beans"](https://arxiv.org/abs/1908.05647);
  Koka's *Perceus*, [Reinking et al. 2021](https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/)):
  when a `match` takes apart a cell that nothing else refers to (count 1) and the branch builds
  a new cell of the same size, overwrite the old one instead of freeing and allocating. `map`,
  `merge`, `zipWith` and most list code then allocate almost nothing. Checking "count is 1" is
  `Rc::get_mut` in Rust.
- **Freeing long lists without recursion**, which the reference evaluator already does
  (a work list); the runtime needs the same.

A tracing garbage collector (as OCaml, V8, Chez have) is the other option. It's much more work
to write in Rust and buys little for a strict language without cycles: Stitchwort values can't
form cycles, so reference counting frees everything.

An arena (allocate everything in one block, free it at the end) is simplest of all and very
fast, but memory never shrinks while running: a long AoC run that builds and drops many lists
would grow without limit. Not recommended as the main strategy.

### 2.5 Effects

Today an effectful computation is data: a `Comp` value that is either `Done x` or
`Call op k` (an operation and what to do with its answer), and a loop (`run_loop`, and its JS
copy) performs `IO` and feeds the reply back. Measured cost in pure code: nothing worth
measuring (evaluator-speed §2). The runtime can keep exactly this: it runs pure code to a
`Comp` value and the same runner loop handles the rest. `Partial` (the `Delay` stepping
machine) is also data, and `run --js` already reimplements its stepping; the runtime does the
same.

What other languages do, for when handlers inside a program become the bottleneck (SW-74):

- **Koka** passes the active handlers down as an extra hidden argument ("evidence") and
  compiles most operations to plain calls
  ([Xie & Leijen 2021, "Generalized Evidence Passing for Effect Handlers"](https://www.microsoft.com/en-us/research/publication/generalized-evidence-passing-for-effect-handlers/)).
- **Effekt** passes handlers as capabilities and compiles to JS, Chez Scheme and LLVM
  ([effekt-lang.org](https://effekt-lang.org/)).
- **OCaml 5** gives each handler its own small stack segment ("fiber") and switches between them
  ([Sivaramakrishnan et al. 2021, "Retrofitting Effect Handlers onto OCaml"](https://arxiv.org/abs/2104.00250)).
  A bytecode machine with its own stack can do something similar later (capture a slice of its
  frames as the continuation `k`), which a closure compiler on the Rust stack can't.

None of this is needed for the first version: AoC programs do a handful of `IO` operations.

### 2.6 Using another project's runtime

The idea: generate code in another language and let its mature compiler or VM run it. The
JS backend is already this. Each option in one paragraph; the
[appendix](#appendix-b-other-runtimes-in-detail) has a table.

- **Chez Scheme** ([cisco/ChezScheme](https://github.com/cisco/ChezScheme), Apache-2.0,
  `nixpkgs#chez` 10.4.1; Racket's fork was merged back into it for 10.0). Idris 2's default
  backend, and the basis of Unison's native runtime. Fast native code, built-in bignums, proper tail
  calls, deep recursion limited only by memory, first-class continuations (good for effects).
  Generating Scheme text would be close to the JS generator. Costs: an external `scheme`
  binary at run time (like Node today), a compile step on each run, and nothing for the
  playground.
- **OCaml via Malfunction** ([stedolan/malfunction](https://github.com/stedolan/malfunction)):
  an untyped input language for OCaml's optimising native compiler
  (`nixpkgs#ocamlPackages.malfunction` 0.7.1), used by experimental third-party backends for
  Idris 1 and Agda. Fast output and Zarith bignums, but needs an OCaml toolchain at run time and
  compile time per program; nothing for the playground.
- **Cranelift JIT** (`cranelift-jit` 0.137, Apache-2.0 with LLVM exception, the code generator
  of Wasmtime; its README still calls the JIT crate "extremely experimental"). A JIT inside the
  `stitchwort` binary, no external tools, fast compilation, and a `tail` calling convention for
  proper tail calls. But
  everything a language runtime needs besides instructions (values, reference counting,
  bignums, the stack, effects) is ours to write in Rust anyway, and it doesn't run in the
  browser (a JIT can't generate code inside WebAssembly).
- **LLVM** (`inkwell` 0.11, Apache-2.0, LLVM 12–23 chosen by a Cargo feature): the best code,
  at the cost of linking LLVM (large, slow to build, a version to match). Roc uses LLVM and Lean
  uses C, but they're compilers whose main product is native code.
- **C** (as Lean 4 and Koka do, with reference counting in a small C runtime): portable, fast,
  and the same C could become WebAssembly via clang. Needs a C compiler at run time.
- **WebAssembly as output** (run natively with `wasmtime`, `nixpkgs#wasmtime` 49; in the
  browser directly): one artefact for both. Tail calls and GC are finished proposals, supported
  by all three major browser engines since about December 2024 and on by default in Wasmtime.
  But a dynamic language runtime in Wasm still
  needs its own memory management (Wasm GC exists but is young), and it's a compiler, not a
  library: the largest effort here.
- **Lua/LuaJIT** (`mlua`, MIT; `nixpkgs#luajit`): small and fast, but numbers are floating
  point (no bignums; 64-bit integers in LuaJIT only as boxed FFI values), and deep recursion is
  limited.
- **The JVM, GraalVM Truffle, the BEAM, GHC Core:** large runtimes for a different purpose;
  startup cost and footprint out of proportion. Not considered further.
- **HVM / Bend**: parallel evaluation based on interaction nets. Bend 2 has itself become a
  dependently typed language with C, CUDA, Metal and JS backends, and describes itself as young.
  Its evaluation model differs from Stitchwort's strict one, and its numbers are `Nat`, `U32`
  and `F32`. Not a fit as a backend.

**Embedding a JS engine** in the `stitchwort` binary (instead of starting Node) would make
`run --js` self-contained:

- **QuickJS** (`rquickjs`, MIT, which binds quickjs-ng; the engine is about 1 MB): measured **8.6× slower than Node** on day 4 (2.3 s vs
  0.27 s), still about 2× faster than today's `run`; but it runs out of stack on lists of
  30,000 elements within a 64 MB stack (§3). It would need a thread with a stack of gigabytes.
- **Boa** (`boa_engine`, pure Rust, an interpreter): easy to build; a third-party benchmark
  puts it well behind QuickJS (unmeasured here).
- **V8** (`deno_core` / the `v8` crate): Node's speed, but adds roughly 40 MB to the binary (a
  report on Deno's forum) and downloads a prebuilt static library at build time
  (`RUSTY_V8_ARCHIVE` can name a local copy, which a Nix build would need).

None of these helps the playground, where the browser already has a fast JS engine, but where
generated JS recurses on a stack the page can't enlarge.

### 2.7 How comparable languages run code

| Language | How programs run |
|---|---|
| Lean 4 | Compiles to C with reference counting and reset/reuse, plus an interpreter. A new code generator (LCNF) runs end to end as of 4.30 (May 2026). |
| Idris 2 | Default backend Chez Scheme; also Racket, Gambit, JS, and RefC (C with reference counting; its docs call it experimental and slower than the Scheme backends). |
| Agda | MAlonzo (to Haskell, compiled by GHC) and a JS backend. |
| Koka | C with Perceus reference counting and reuse; effect handlers by evidence passing; also JS. |
| Unison | Content-addressed like Stitchwort. First an interpreter in Haskell, then (from 2022) a native runtime through Chez Scheme, reported as hundreds of times faster on arithmetic loops. |
| Roc | LLVM for optimised builds; reference counting with Perceus-style reuse; the compiler is being rewritten from Rust in Zig (2025). |
| Effekt | JS and Chez Scheme from its core IR; an LLVM backend (ICFP 2025). |
| Dafny | Compiles to C#, Java, JS, Go, Python and C++. |
| F* | Extracts to OCaml; its Low* subset to readable C via KaRaMeL. |

So two patterns: **reuse a mature runtime** (Chez, GHC, OCaml, JS, C compilers), or **write a
native compiler with reference counting** (Lean, Koka, Roc). Nobody in this list uses its
type checker's evaluator to run programs. Stitchwort's extra constraint is that the same
runtime must also work in a static web page. That rules out every option needing an external
compiler or VM at run time, and leaves JS or WebAssembly.

## 3. What was measured

Apple M4 Pro, release build of `main` at `447b340`, **machine shared with other jobs (load
average 7–14)**, so times vary by up to ±30% between runs; the best of three is shown where
repeated. Full numbers in [appendix A](#appendix-a-measurements).

**Day 4** (the real input), one run each:

| How | Time (s) | vs `run` |
|---|---:|---:|
| `stitchwort run` (includes 0.22 s of checking) | 5.48 | 1× |
| `stitchwort run --js` (includes checking and Node's start) | 0.61 | 9× |
| the generated JS, Node 22 alone | 0.27 | |
| the same JS under QuickJS 2026-06-04 | 2.32 (user) | |
| the same JS under quickjs-ng 0.17.0 | 2.34 (user) | |

**A merge sort of 100,000 numbers** (`List.sortBy Nat.compare` over scrambled numbers, then
`map` and a sum; a scratch `.sw` file):

| How | Time (s) | vs `run` |
|---|---:|---:|
| `stitchwort run` (minus 0.24 s of checking) | 6.0 | 1× |
| the generated JS, Node 22 alone (minus Node's 0.08 s start) | 0.54 | 11× |
| QuickJS, both versions | stack overflow (also at 30,000) | |
| **closure-compiled Rust prototype** | **0.39–0.56** | **11–15×** |

At 10,000 numbers: `run` 0.88 s (with checking), Node 0.14 s, QuickJS 0.31 s, prototype 0.04 s.

**The prototype** (scratch, 350 lines of Rust, no dependencies) is option 2.2(a) on a
hand-written erased IR of exactly the prelude's `List.sortWith` / `pushRun` / `buildRuns` /
`mergeRuns` / `merge`, `List.map`, `List.rangeFrom` and `Nat.compare`: saturated calls, flat
closures for the comparator, `if` as a case on `Bool`, numbers as `i64` with overflow checks,
`Rc` for constructor cells, no reuse. It printed the same results as `stitchwort run` at all
three sizes. **Caveats:** the IR was written by hand, not generated; no bignum fallback is
implemented (the overflow check is there, the fallback panics); it recurses on a 4 GB Rust
stack, which the playground can't have; there are no resource limits; one benchmark. A real
bytecode machine with its own stack would likely be somewhat slower than this (a guess:
0.5–1× its speed).

**What it shows:** the gain comes from the IR (erasure, saturated calls, no copied
environments, cheap `if`), not from native code: a plain Rust interpreter of that IR runs at
V8's speed on this allocation-heavy code. That's the case for building the runtime in Rust
rather than adopting another one.

## 4. Recommendation

Ranked by gain for the work.

### Now (no new work): `run --js` for heavy programs

`run --js` gives 9–20× today. **Don't make it the default** (D385): it needs Node on the
`PATH`, behaves differently when resources run out (Node's stack and memory limits rather
than `E-RESOURCE` from Stitchwort's own limits), and a default that changes with what's
installed is surprising. The runtime below replaces it as the fast path in a few weeks of lanes.

### Medium term (recommended): a Rust runtime, `stitchwort-rt`, shared by CLI and playground

1. **Stage 1, the erased IR** (2–3 lane-days; Opus design, Sonnet build). A new crate
   lowering checked definitions to: erased, closure-converted, saturated calls, slot-numbered
   variables, `match` as a switch on constructor tags, `if`/`==` specialised, natives by
   index, compact text and `Int`/`Text` natives as the JS backend binds them. A pretty-printer
   for it, for tests and debugging.
2. **Stage 2, the machine** (3–4 lane-days; Opus). A bytecode interpreter with its own frame
   stack: values with small numbers inline and `BigUint` fallback, `Rc` cells, tags for
   nullary constructors (`Nil`, `True`) with no allocation, iterative freeing, tail calls,
   resource limits (frames, memory) reported as `E-RESOURCE`. The `Comp` runner and the `Delay`
   stepping loop as in `run --js`.
3. **Stage 3, wiring and differential tests** (1–2 lane-days; Sonnet). `stitchwort run` and
   the playground use it behind a switch first (`run --rt`, for example). Every `examples/` and
   `aoc/` `main` and every bench program runs on both the runtime and the reference evaluator
   and must give the same output, as the existing differential tests do for JS. The reference
   evaluator is the oracle.
4. **Stage 4, tuning** (2 lane-days; Opus/Sonnet). Reuse in place (Perceus/Lean-style), a few
   combined instructions for common sequences, measurement against `bench/baseline.toml`.

Expected: 8–15× over today's `run` (anchored by the prototype's 11–15×, discounted for an
explicit stack and real bignum checks), i.e. close to Node. In the playground, WebAssembly
typically runs at a fraction of native speed (a guess: 1.5–2× slower), but the gain over the
playground's current evaluator should be similar, and deep recursion stops depending on the
browser's stack.

Then `run` uses it by default (D386), with the reference evaluator still available
(`run --reference`) and in tests.

**What stays trusted:** nothing changes for proofs. The kernel and its evaluator still check
everything; the runtime only affects what a program prints, as the JS backend does today
(DESIGN.md §12). It is checked by testing against the reference evaluator, not by proof.

**Risks:** (1) two evaluators disagreeing: the differential tests, run in `nix flake check`,
are the guard; (2) bignum fallback bugs: test arithmetic near 2^63 and 2^64 against the
reference and the natives' own definitions; (3) effects and `Partial`: reuse the JS runner's
design, which is already differential-tested; (4) a second consumer of erasure: share it with the
JS backend rather than writing it twice.

### Long term (only if needed): native code from the same IR

If some programs still need more (the day 2 brute force takes 77 s even under Node), the IR
can feed a code generator. Candidates, cheapest first: **Chez Scheme text** (closest to the JS
generator; bignums and deep recursion for free; needs `scheme` installed), **C with a small
reference-counting runtime** (Lean/Koka's route; needs a C compiler), **Cranelift** (no
external tools; most runtime work). Expected 2–5× over the bytecode machine. Not before the
runtime has been in use for a while: an algorithm change usually gains more on AoC than any
backend (day 2's brute force over 1.9 million ids is the example).

## As built (stage 1)

SW-230, 21 October 2026. A new crate, `crates/rt` (`stitchwort-rt`). Nothing runs on it
yet: `run` is unchanged.

**Shared with the JS backend (D389).** The JS backend now depends on `stitchwort-rt` for:
the native tables and their binding by content hash (`natives.rs`: `TextNative`,
`IntNative`, `bind_text_natives`, `bind_int`, the `Nat`/`Int`/`Text` representation hashes,
and a `Representation` that both build from them); and erasure (`erasure.rs`: `def_shape`,
which parameters and results are erased, `reachable`, `text_literal`,
`is_done_continuation`). `stitchwort_js` re-exports what was public before. The JS output
is unchanged (its snapshots and differential tests pass as before); the natives' JS code
stays in `crates/js`.

**The IR** (`ir.rs`), in short:

```text
program  = global* lambda* type* entry
global   = fn name(v0..vn-1) = expr      runtime parameters only, n ≥ 1
         | const name = expr             no runtime parameters: computed when first used
         | native name = %op/n           a native operation as a value
lambda   = λi[captures](v0..vn-1) => expr     consecutive lambdas are one, of arity n
expr     = vN | cN | name | erased | literal | done-k
         | name(expr*)                   saturated call of a global
         | %op(expr*)                    native operation, all arguments
         | pap name(expr*)               a global with too few arguments
         | apply expr(expr+)             a function value (eval/apply)
         | λi[c0 = expr, …]              a closure
         | Ctor(expr*)                   runtime fields only
         | let vN = expr; expr
         | match vN: T { Ctor(field: vM, …) => expr; … }    T a data type, Nat, Int or Text
         | switch vN { 3 => expr; …; _ => expr }           a number pattern
         | if expr then expr else expr
         | unreachable
literal  = 42 | int(-5) | "text" | chars"abc"
```

`vN` is slot `N` of the frame (parameters first), `cN` a value the closure captured. A
match binds only the fields its arm uses. Natives (`%op`) are the kernel's `Nat` natives,
the `Int` and `Text` natives where they bind, `Delay`'s constants (built as data, run by
the runner as `run --js` does), and three of the IR's own: `NegSucc`, and `IntEqual` and
`TextEqual` for `toBool (Int.decEq a b)` and `toBool (Text.decEq a b)` (`Nat.decEq` fuses
into the kernel's `Nat.equal` the same way). `Bool.ifThenElse c (_ => a) (_ => b)` is an
`if`. A beta-redex `(x => b) a`, which the elaborator writes for `main` and for bound
decisions, is a `let` (dropped if the body doesn't use it). An example, from
`crates/rt/tests/snapshots/lower__a_lambda_capturing_variables.snap`:

```text
fn Main.scale(v0, v1, v2) {3 slots} =
  Std.List.map(λ0[c0 = v0, c1 = v1](v0) {1 slots} =>
    %Nat.add(%Nat.mul(c0, v0), c1), v2)
```

**API:** `lower_main(g, limits, main_term)` (the term `run` runs), `lower_global`,
`lower_definitions`; `Program` prints the listing above (`Display`) and checks itself
(`Program::validate`: slots read are bound and in the frame, a slot isn't rebound while
in scope, arities, captures, constructor fields).

**Tests** (`crates/rt/tests/lower.rs`, `dev/t rt`, about 25 s): every runnable `main` in
`examples/accept` and `examples/extract` (9), every example project (none has a `main`)
and every AoC `main` (7) lowers; so does every definition of each of those programs and of
the whole library, and each program is validated. A small reference interpreter for the
IR (`tests/interp/`, test-only, pure code only) runs every `test` of those programs and
of the library on the IR and compares the outcome with `stitchwort test`: about 1,100
tests agree. It found one lowering bug (a beta-redex's later argument reusing an earlier
parameter's slot). Seven IR snapshots: recursion on lists, a record, an effectful `main`
with `IO`, text and `Int` natives, `==`/`<` on each native type, a local `def`, and a
lambda capturing variables.

**What turned out differently from §2.1 and §5:**

- `==` fuses as described only when the decision is a native `decEq` directly. `<` on
  `Nat` is `toBool (Nat.decLessThan a b)`, a call that computes `Bool.decTrue (Nat.leq (a
  + 1) b)`; `==` on `Char` goes through `Char.decEq`'s definition; and `<` on `Text` (any
  `Ord` method) is a dictionary projection, `apply Std.Ord.decLessThan(Std.Text.instOrd)(a,
  b)`, then a closure call. The JS backend does the same. Inlining small definitions and
  "case of known constructor" on constant dictionaries would remove these; they belong to
  stage 4 (or a stage 1b), not needed for correctness.
- Constants: the JS backend has two conventions for a definition without runtime
  parameters (a value computed when the module loads, or a thunk run at each use, for
  case trees like `absurd` and members of groups). The IR has one: computed when first
  used, then kept, which is right for both.
- The runtime needs the native `Nat` and `Text` representations (as `run --js` needs
  native text); lowering refuses a prelude whose `Nat` or `Text` hash differs. `Int` may be
  either.
- Stage 2 will need to know which data types the natives build (`Bool`, `Option`, `Pair`,
  `Ordering`, `Decidable`, `List`, `Char`) and the runner's (`Comp`, `Plus`, `IO`…), as the
  JS runner's `SHAPE` table does; the IR doesn't record them yet.
- Effort: under one lane-day, against the 2–3 estimated.

## As built (stage 2)

SW-231, 22 October 2026. The machine that runs the IR, in `crates/rt`. It isn't wired into
`stitchwort run` or the playground yet (stage 3); a measuring binary,
`cargo run --release -p stitchwort-rt --example rt_run -- FILE.sw` (or `-- PROJECT-DIR
Name.main`), runs a `main` on it.

**Code** (`code.rs`). Each body (a global function or constant, a lambda, the entry) is
compiled to a flat list of *register* instructions (§2.2b's register variant). A frame is a
window of registers: the IR's slots first, then temporaries. Instructions name the registers
they read and write; a call's arguments are a list of registers, so a variable is passed
without a copy first. The instructions:

```text
Move, Const (from the constant pool), Captured, Global (constant or function value)
Call g / TailCall g, Apply f / TailApply f (eval/apply), Prim op, Pap g, Closure λ, Ctor tag
Switch (by tag, a jump table), Field i, NatCase/NatPred, IntCase/IntOfNat/IntNegSucc,
TextChars, NumSwitch, JumpIfFalse, Jump, Return, Unreachable
```

Expressions in tail position compile to `TailCall`/`TailApply`/`Return`, and a `match` or
`if` in tail position has no join: each arm returns.

**Values** (`value.rs`), three words each:

- `Nat` in a `u64`, `Int` in an `i64`, or a `BigUint`/`BigInt` when the number doesn't fit.
  Each number has exactly one form, so equality is structural. Arithmetic is on machine
  integers with overflow checks, falling back to big numbers only when a result doesn't fit
  (`prims.rs`). The natives compute exactly what the kernel's and the prelude's definitions
  compute: `Nat` subtraction stops at 0, `Nat.divFuel` gives its fuel for a zero divisor,
  `Int` `/` and `%` are Euclidean, `tdiv`/`tmod` truncate and `fdiv`/`fmod` round down. A
  division by zero can't happen: each takes a proof that the divisor isn't 0.
- A constructor without runtime fields (`Nil`, `True`, `None`, a `Yes` whose proof is erased)
  is just its tag; one with fields is its tag and one `Rc<[Value]>` (one allocation).
- Text is an `Rc<str>`. A function value is a global with no arguments, a closure (lambda and
  captured values), a partial application, or `y => Done y`. A `Delay` is data the runner
  looks inside.
- Freeing never recurses: the last reference to a long list, or a long chain of closures, is
  freed with a work list (`Drop` for the fields, closures and `Delay`s).

**The machine** (`machine.rs`). All frames' registers are one `Vec`, and frames are a `Vec` of
small records (code, position, base register, closure, where the result goes), so a
program's recursion is heap memory, never Rust stack: the same in the CLI and in
WebAssembly. A saturated known call pushes a frame directly; a call of a function value goes
through eval/apply (too few arguments make a partial application, too many call with what it
takes and apply the result to the rest). A tail call replaces the frame. A constant is
computed when first used and kept. `Text.fold`, the one native that calls a function, steps
through the machine like a call. Limits: each frame entered is a step, and the steps between
two operations or ticks, and the frames pending, are bounded by the session's limits (its
work limit and its 2,000,000 frames); running out is `E-RESOURCE` with the reference
runner's messages and diagnostic.

**Effects** (`run.rs`). `run_main(program, limits, input, output)` runs `main` as
`Session::run_main` does: the `Delay` stepping of `stitchwort_core::step` (the same frames
and rules, on the machine's values), each `IO` operation performed for real and its reply fed
back, output flushed before each read and at the end, a tick limit for tests
(`run_main_with`). `RunError` and the input reading (`read_line`, `read_all`) moved from the
driver to `stitchwort_rt::host`, and the driver now uses them from there, so the two runners
read input and report errors identically.

**The shape table** the stage 1 note asked for is `Program::shapes`: the tags of the
constructors natives and the runner build or take apart (`Bool`, `Option`, `Decidable`,
`List`, `Pair`, `Char`, the unit, `Comp`, `Plus`, `Rec`, `SigMap`, `IO`'s operations), found
in the checked program's prelude by the registry when lowering, each checked to have the
runtime fields the runtime expects. `Ordering`'s tags are fixed by the content hashes of
the natives that build it.

**Tests** (`crates/rt/tests/machine.rs`; run in release, about 25 s), with the reference
evaluator as the oracle:

| What | Agree |
|---|---:|
| `main`s of `examples/accept` and `examples/extract`, each with three inputs (`run_js.rs`'s): output and how the run ends | 10 |
| AoC mains on their real inputs (also the known answers) and example inputs | 7 |
| `test`s of every example file | 934 |
| `test`s of the AoC project | 101 |
| `test`s of the library | 95 |

Plus: `Nat` and `Int` arithmetic, comparison, division, matching and conversion around 2^63
and 2^64, both ways (52 lines of results); a list of 1,000,000 built and summed by non-tail
recursion (a million frames deep); a recursion beyond the frame limit is `E-RESOURCE` after
the output before it; a 3,000,000-step tail loop within 100 frames; partial application,
over-application and closures; freeing a 2,000,000-element list and a 2,000,000-deep closure
chain. No disagreement was found.

**Measurements.** Apple M4 Pro, release builds, one run each, load average 3.2–3.6 (other
lanes running). Real time, including checking (0.2–0.45 s) for every column:

| Program | `run` (s) | machine (s) | of which running | `run --js` (s) | machine vs `run` |
|---|---:|---:|---:|---:|---:|
| AoC day 4 | 5.04 | 0.70 | 0.37 | 0.59 | 7× (14× running) |
| merge sort, 100,000 | 5.77 | 0.66 | 0.44 | 0.83 | 9× (13×) |
| day 1 brute force | 5.39 | 0.76 | 0.29 | 1.03 | 7× (17×) |
| day 2 brute force | `E-RESOURCE` after 2.8 (too deep) | 23.0 | 22.7 | 66.5 | — (2.9× faster than Node) |

The merge sort's peak memory: 94 MB on the machine, 232 MB under `run`.

**What turned out differently from §4 and §5:**

- Speed: the machine runs at about Node's speed or better, where the note expected 0.5–1×
  the closure prototype; on the merge sort it matches the prototype (0.44 s against
  0.39–0.56 s) with an explicit stack and real bignum checks. The day 2 brute force, 77 s
  under Node in §4, takes 23 s; under `run` it now runs out of frames.
- A value is three words, not two: a constructor's tag sits beside its one `Rc<[Value]>`, so
  a cell is one allocation (two words would need a second allocation or a custom thin
  pointer).
- No separate memory limit: like the reference runner, the machine bounds frames and steps;
  memory follows from the frame limit, and values on the heap aren't bounded (the reference
  evaluator doesn't bound them either).
- The step limit counts frames entered, not the reference evaluator's steps, so the two can
  run out at different points: a program that runs out under `run` (day 2's brute force,
  which recurses more deeply there) may finish on the machine. Stage 3 must decide whether
  `E-RESOURCE` should match exactly (it can't, without counting the same thing) or only be
  reported the same way.
- `RunError` moved to the runtime crate so that both runners share it; the driver
  re-exports it, and `RunError::diagnostic` takes `main`'s span (a `&Main` still works).
- Stage 1's tests made their sessions with `Session::new()`, whose limits are for a 2 MiB
  stack, though they run on a 256 MiB thread: in a debug build, checking the AoC project and
  `examples/extract/names.sw` ran out of nesting depth, so `every_aoc_main_lowers` failed in
  a debug `dev/t rt` (it passed in release, as the gate builds it). They now use
  `Session::for_stack`, as the machine's tests do.
- Effort: under one lane-day, against the 3–4 estimated.

## As built (stage 3)

SW-232, 22 October 2026. The machine is the default: `stitchwort run` and the playground's
Run tab (and each project day's) run `main` on it. `stitchwort run --reference` runs it on
the type checker's evaluator as before (the oracle, and a way to check a suspect result);
`--js` is unchanged, and `--reference` and `--js` can't be combined.

**Wiring.** `Session::run_main_fast` (`crates/driver/src/run.rs`) lowers `main`'s term
(`stitchwort_rt::lower_main`) and runs it (`stitchwort_rt::run_main`) with the same input
reading, output flushing and `RunError`s as `Session::run_main`; the CLI and the web crate
call it where they called `run_main`. A failure to lower (nesting too deep for the session's
stack limit, or an internal error) is a new `RunError::Lowering(Diagnostic)`, reported as
that diagnostic. Exit codes, `E-RESOURCE`'s message and label ("while running this
program"), `E-IO`, and what is printed before an error are as before; the playground's
`E-OUTPUT` and `E-INPUT` limits are enforced by the same `Write`/`BufRead` wrappers, so they
work unchanged, and the worker's timeout and Stop terminate the worker as before (the
runaway-run browser test passes). Streaming is as before: the machine writes each `print`
to the writer as it happens.

**What stays on the reference evaluator, and why.**

- `stitchwort test` and the playground's Tests tab: a test's result is a claim the cache,
  the gate and the library rely on, and the evaluator is the trusted one (the machine, like
  the JS backend, can only be differentially tested). Tests are small and their results are
  cached by content hash (the key would have to include the runner if two runners could
  disagree); a failing comparison test also shows both sides, which needs the evaluator's
  values. Running the 1,100 tests on the machine is already part of the differential tests.

  **Update (24 October 2026, SW-412, provisional pending Matt's decision):** `stitchwort test`
  now runs tests on the machine (`Session::run_tests_fast`), because real-input tests weren't
  small: day 9's took 70 s on the evaluator and 2 s on the machine. A test the machine can't
  lower or finish runs on the evaluator, which also still shows a failure's sides; results
  are cached under a key with the runner in it (`modes` plus `m`); `stitchwort test
  --reference` runs on the evaluator as before. The playground's Tests tab, the library
  tests and `Session::run_tests` stay on the evaluator, and `crates/rt/tests/machine.rs`
  still compares the two on every test except the AoC real-input ones.
- `stitchwort eval`, the REPL and the Evaluate tab: they print a value of any type, with
  types, proofs and functions in it, from the evaluator's values; the machine's are erased.

**Differential tests** (the reference evaluator is the oracle; `dev/t rt`, `dev/t cli`):
`crates/rt/tests/machine.rs` as in stage 2, plus the two `bench` programs that have a
`main` (20,000 prints; a record with a proof field over 200 input lines), and both runners
running out of resources (work and frames) after the same output. New:
`crates/cli/tests/run_reference.rs` runs the built command both ways: every example `main`
on three inputs (same output, exit code and error text), AoC day 4 by its full name,
`readLine`/`readAll` on ten edge-case inputs, a type error, a recursion a million frames deep
(machine only), `E-RESOURCE` (both), and the `--reference`/`--js` conflict. The existing
`run.rs`, `run_js.rs` (`--js` against the default, now the machine) and `aoc_answers.rs`
tests run through the machine's path. Every comparison agrees: no mismatch was found, which
is why the default switched (D386). A browser test runs a non-tail recursion a million calls
deep in the playground.

**Resource limits.** The machine's step count is frames entered, not the evaluator's steps,
so the same program may stop at different points (day 2's brute force gives `E-RESOURCE`
after 2.7 s under `--reference` and finishes in 23 s on the machine). Only the way it's
reported is the same; tests check that, not the point.

**Playground.** The WebAssembly bundle grew from 3,584,945 to 3,709,918 bytes (+125 KB, 3.5%;
gzipped 1,293,638 to 1,339,305, +45 KB). The reference evaluator already kept its pending work
on the heap, so a deep recursion that "failed before" doesn't: a million calls deep ran on the
old build as well. The gain is speed, and recursion deeper than the evaluator's memory allows.

**Measurements** (release build, Apple M4 Pro, load average about 4–5, real seconds, each
including checking):

| Program | `run` (machine) | `run --reference` | `run --js` |
|---|---:|---:|---:|
| AoC day 4 | 0.77 | 5.01 | 0.62 |
| merge sort, 100,000 | 0.68 | 5.85 | 0.84 |
| day 1 brute force | 0.77 | 5.38 | 1.06 |
| day 2 brute force | 23.1 | `E-RESOURCE` after 2.7 | 66.8 |

## As built (stage 4)

SW-233, 22 October 2026. Tuning, one commit per change, each measured and run against the
differential tests. `bench/baseline.toml` was re-recorded on `main` first (its `examples` and
`extract-js` inputs had changed and `check-closed-*` had drifted by about 10%); it measures
the reference evaluator and the checker, which this stage doesn't touch, so it doesn't move.

**Where the time went** (macOS `sample` at 1 ms, a build with line tables, and a counting
build for instruction pairs):

- Day 2's brute force: about 55% in `malloc` and `free` and dropping values. `Text.take`,
  `drop` and `contains` are library definitions over `List Char`, so each call turns a text
  into a list of character cells (`TextToList`) and back; and every cell was allocated twice
  (`Value::data` built a `Vec`, then copied it into an `Rc<[Value]>`).
- The merge sort: the comparison is a closure called through eval/apply (an argument vector
  per call, then three frames: the closure, `Nat.compare`, `Ordering.isLessEq`), plus a
  new cell for every cell `merge` takes apart, and dropping each frame's registers.
- Day 4: many tiny calls: `Decidable.toBool (Nat.decLessThan 4 n)`, `Cell.%decEq` then
  `toBool`, `Pair.fst`/`snd`, record projections, `Vec.headOr`.
- Instruction pairs (merge sort of 100,000): `Switch → Unpack` 3.5 million, `Prim →
  JumpIfFalse` 2.8 million, `CtorReuse → Return` 1.8 million.

**What changed:**

1. **One allocation per cell** (`value.rs`): `Value::data` takes an array.
2. **Moves, early drops and reuse in place** (`code.rs`, Perceus/Lean-style). The compiler
   computes which slots are read later. An operand read for the last time is moved out of
   its register (`MOVE` on the register), so a list passed on stays uniquely owned; a
   variable a branch doesn't need is dropped as the branch starts. A match whose scrutinee
   the arm doesn't need again takes the fields out (`Unpack`): if the cell is uniquely owned
   they're moved, and if the arm builds a constructor with as many fields, the emptied cell
   is a reuse token that `CtorReuse` fills in place. A variable known (from an enclosing
   match) to be a constructor can be dropped into a token too (`DropReuse`, as `merge`
   needs). Each constructor on a path claims its own token. A shared cell is never changed:
   its fields are copied and it's left alone.
3. **A simplifier for the IR** (`opt.rs`, run by lowering on every program): inlining small
   non-recursive functions; beta for a closure applied where it's made or bound; known
   constructors (from a `let`, an enclosing arm, a literal, or a constant whose value is a
   constructor, such as an instance dictionary) take their arm; case of case for small
   continuations; a match on `Bool` is an `if`, and `if c then True else False` is `c`; a
   match on a `decEq` decision on native values is an `if` on the native equality; applying
   a global, a partial application or a closure literal is a direct call; a lambda capturing
   constants gets a copy with them substituted; a recursive function called with known
   function arguments (`map scramble`, `merge`'s comparison, `foldLeft`'s closure) gets a
   copy with them substituted, whose recursive calls call the copy; `Nat` operations on
   literals are computed; and a `let` bound to a single-arm match (a projection) moves into
   the arm. So `a < b` on `Nat` is `%Nat.leq(a + 1, b)`, `==` on `Char` compares the codes,
   `Ord.decLessThan` on a known instance is a direct call, and `sortBy Nat.compare` sorts with
   `merge` specialised to `if a == b then True else a <= b` inline. Each body's slots are
   renamed apart first and packed again at the end; lowering still takes about 1 ms. Bounds:
   functions up to 24 nodes are inlined, 64 copies of functions up to 200 nodes, fuel per
   body, and a body nested more than 1,000 deep is left as lowered. The JS backend doesn't
   use this IR, so its output is unchanged.
4. **Applying a known-arity function** pushes its frame from the caller's registers, as a
   direct call does, with no argument vector.
5. **Shared ASCII character cells**: `TextToList`, `uncons` and `fold` reuse one cell per
   ASCII character (safe with reuse: a shared cell is never changed).
6. **Frame teardown** checks inline which registers own anything, instead of a drop call each.
7. **A combined instruction**, `Test`: an `if` on a native comparison (`Nat` `<=`, `==`;
   `Int` `==`, `<`, `<=`; `Text` `==`, `isEmpty`) compares numbers that fit a word inline and
   jumps, without making a `Bool`. The other frequent pairs (`Switch → Unpack`, `CtorReuse →
   Return`) would save one dispatch each; not worth it at these sizes.

The listing printer writes a lambda that makes a closure of itself (possible after inlining)
once. The liveness is computed once per body, bottom up: asked afresh at each level, it was
quadratic in nesting depth (a list literal of 20,000 numbers took 1.9 s instead of 0.35 s;
now 0.41 s).

**Measurements** (release builds, Apple M4 Pro, median of 3 runs, load average 3–6 with other
lanes running; seconds). Running time from `rt_run`, which times checking and running
separately; wall time is `stitchwort run`:

| Program | run, before | run, after | | wall, before | wall, after | checking |
|---|---:|---:|---:|---:|---:|---:|
| AoC day 4 | 0.373 | 0.192 | 1.9× | 0.73 | 0.54 | 0.32 |
| merge sort, 100,000 | 0.438 | 0.159 | 2.8× | 0.68 | 0.39 | 0.21 |
| day 1 brute force | 0.286 | 0.193 | 1.5× | 0.76 | 0.68 | 0.46 |
| day 2 brute force | 22.84 | 11.48 | 2.0× | 23.09 | 11.80 | 0.31 |

By step (running time; the load varied, so differences of a few per cent are noise):

| Change | day 4 | sort | day 1 | day 2 |
|---|---:|---:|---:|---:|
| before | 0.373 | 0.438 | 0.286 | 22.84 |
| one allocation per cell | 0.379 | 0.435 | 0.285 | 18.87 |
| moves and reuse | 0.390 | 0.371 | 0.245 | 16.35 |
| simplifier | 0.256 | 0.256 | 0.264 | 13.59 |
| known-arity apply | 0.236 | 0.223 | 0.231 | — |
| ASCII cells | 0.239 | 0.226 | 0.228 | 12.08 |
| function copies, folding | 0.206 | 0.183 | 0.200 | 11.93 |
| frame teardown | 0.195 | 0.168 | 0.195 | — |
| `Test`, liveness once per body | 0.192 | 0.158 | 0.192 | 11.48 |

The merge sort's peak memory: 85 MB, from 95 MB. Allocation has all but gone from its profile
(5 of about 1,400 samples): each cell `merge` builds reuses one it took apart.

**Checking is now most of the wall time** for programs like these: 0.21–0.46 s of 0.39–0.68 s
(55–68%), against 0.16–0.19 s of running. Day 1's file checks for 0.46 s. Faster checking (or
caching a checked prelude across runs) would now gain more than the machine.

**What's left, and what turned out differently from §4 and §5:**

- The gain is 1.5–2.8× on running, not the "a few combined instructions" the plan expected:
  most of it came from the simplifier and reuse, which the plan put under stage 4 as
  "reuse in place" and stage 1 as "a stage 1b" (inlining, constant dictionaries).
- Day 2's remaining time is still mostly character lists: `Text.take`, `drop` and `contains`
  are library definitions over `List Char`. Native versions bound by content hash, as the
  other text natives are, would remove that; they'd need registry entries and JS code as
  well, and each is a trusted native, so that's a decision rather than tuning (not done).
- The differential tests (every example and AoC `main` both ways, the IR interpreter over
  about 1,100 tests, the validator over every lowered definition) all passed throughout, but
  reviewing the simplifier found a bug they missed: a variable known to be a constructor
  counted as true or false by its tag alone, so `if c then x else y` with `x` known `Some …`
  and `y` known `None` became `c`. Fixed (a known constructor carries its type), with a
  test. The simplifier is where a wrong answer could now come from; more small programs
  run both ways would be cheap insurance.
- The step count (frames entered) falls with inlining, so a program runs further before
  `E-RESOURCE` than before; only the way it's reported is the same, as in stage 3.
- Effort: under one lane-day, against the 2 estimated.

## Decisions

| ID | Question | Recommendation |
|---|---|---|
| D381 | Build a separate, untrusted runtime in Rust for running programs (an erased IR plus an interpreter), rather than making the type checker's evaluator faster or adopting another language's runtime? | [Yes: it's the only option that is fast, self-contained and also works in the playground] |
| D382 | Interpreter shape: bytecode with its own frame stack, rather than closures on the Rust stack? | [Bytecode with its own stack: deep recursion must work in the browser, where the stack is tiny; the closure prototype was a speed reference, not the design] |
| D383 | Values: small numbers inline with `BigUint` fallback, `Rc` cells, reuse in place in stage 4? | [Yes] |
| D384 | Effects: keep `Comp` as data with the existing runner loop for now; native handler support only if SW-74's benchmarks show handlers are slow? | [Yes] |
| D385 | Make `run --js` the default meanwhile? | [No: keep it explicit; it needs Node and reports running out of resources differently] |
| D386 | When the runtime passes the differential tests, make it the default for `run` and the playground, keeping the reference evaluator behind `run --reference` and in tests? | [Yes: done in stage 3; every differential test agreed] |
| D387 | Embed a JS engine (QuickJS or V8) to make `run --js` self-contained? | [No: QuickJS is 8× slower than Node and needs a huge stack; V8 is too large and hard to build under Nix] |
| D388 | Native code (Chez, C, Cranelift, LLVM)? | [Not now; revisit from the same IR if programs need it, Chez text or C first] |
| D389 | Share the erased IR's lowering with the JS backend (eventually generating JS from it)? | [Yes for erasure and natives from the start; moving the JS generator onto the IR later, as its own lane] |

## Appendix A: measurements

All on `447b340`, Apple M4 Pro, other lanes running (load average 7–14). `/usr/bin/time -p`.
Scratch files under the session scratchpad (`fast-runtime/`), not committed.

**Day 4**, `aoc/` with `inputs/day04.txt`, output `Part 1: 1397`, `Part 2: 8758` everywhere:

| Command | real | user |
|---|---:|---:|
| `stitchwort run Aoc.Day04.main` | 5.48 | 5.33 |
| `stitchwort run --js Aoc.Day04.main` | 0.61 | 0.57 |
| `node run.mjs` (the generated files, kept with `STITCHWORT_RUN_JS_DIR`) | 0.27 | 0.28 |
| `qjs` (QuickJS 2026-06-04), `--stack-size 60000000`, `ulimit -s 65520` | 3.52 | 2.32 |
| `qjs` (quickjs-ng 0.17.0), same | 2.37 | 2.34 |

The QuickJS runs used the generated `program.mjs` with its two Node imports replaced by a 40-line
shim (`Buffer`, `TextDecoder`, `fs.readSync`/`writeSync` over QuickJS's `std`).

**Merge sort benchmark** (`scramble x = (x * 7919 + 13) % 1000003` over `List.range n`, sorted
with `List.sortBy Nat.compare`, then `List.map (x => x + 1)` and a tail-recursive sum).
`stitchwort check` alone: 0.24 s.

| n | `run` (real, incl. check) | Node alone (real, incl. 0.08 s start) | QuickJS / quickjs-ng | Prototype (compute only) |
|---:|---:|---:|---:|---:|
| 10,000 | 0.88 | 0.14 | 0.40 / 0.40 | 0.038 |
| 30,000 | 1.79 | 0.20 | stack overflow / crash after 0.85 s | 0.115 |
| 100,000 | 6.01, 6.74, 6.54, 6.29 | 0.63, 1.41, 0.64, 0.62 | stack overflow | 0.92, 0.47, 0.56, 0.50, 0.39 |

The first prototype run at 100,000 (0.92 s) and Node's 1.41 s coincide with load spikes; the
others agree within ±20%. Results printed: 4990372243, 14983989689, 49992816518 (n = 10,000,
30,000, 100,000), the same from every engine that finished. The prototype's peak memory at
100,000: 184 MB.

## Appendix B: other runtimes in detail

"Browser" means the option could also serve the playground. Versions as of October 2026.
Speed is relative to a good bytecode interpreter of the erased IR (§2.2b), and is a rough
expectation, not a measurement, except where marked.

| Option | How Stitchwort would target it | Licence | In Rust / Nix | Bignums | Deep recursion | Effects | Browser | Speed | Effort |
|---|---|---|---|---|---|---|---|---|---|
| Bytecode VM in Rust (recommended) | erased IR → bytecode | ours | it is Rust | `BigUint` fallback | own stack: memory only | `Comp` + runner; one-shot continuations possible later | yes (Wasm) | 1× (guess: 0.5–1× the closure prototype, which matched Node) | 8–11 lane-days |
| Closure compilation in Rust | erased IR → Rust closures | ours | it is Rust | same | Rust stack: big thread natively, not in the browser | same, but no stack capture | only with shallow recursion | 1–2× | 4–6 lane-days |
| Node (today's `run --js`) | JS text | MIT | Node in the dev shell | `bigint` | 2 GB worker stack | `Comp` runner in JS | browser JS has a fixed stack | measured ≈ 1× | done |
| QuickJS (`rquickjs`) | the same JS, embedded | MIT | crate, builds C | `bigint` | C stack: needs a huge thread stack | same | no (browser has its own engine) | measured ≈ 8× slower than Node | 2–3 lane-days |
| V8 (`deno_core`/`v8`) | the same JS, embedded | MIT/BSD | crate, ~40 MB prebuilt download | `bigint` | settable | same | no | ≈ Node | 3–5 lane-days, Nix work |
| Boa | the same JS, embedded | MIT/Unlicense | pure Rust | `BigInt` | interpreter | same | no | slower than QuickJS (third-party) | 2–3 lane-days |
| Chez Scheme | Scheme text, run by `scheme` | Apache-2.0 | external binary; `nixpkgs#chez` 10.4.1 | native | heap-allocated stack segments | `call/cc`, one-shot continuations | no | 2–5× faster | 4–6 lane-days |
| OCaml via Malfunction | s-expressions → `ocamlopt` | LGPL (OCaml), Malfunction MIT | external toolchain; `nixpkgs#ocamlPackages.malfunction` 0.7.1 | Zarith | OCaml 5 grows its stack | OCaml 5 handlers | no | 2–5× faster | 5–8 lane-days |
| C (+ RC runtime, Lean/Koka style) | C text → clang | ours | needs a C compiler; Boehm GC is `nixpkgs#boehmgc` if not RC | ours (or GMP) | C stack unless designed otherwise | evidence passing (Koka) | via clang → Wasm, with work | 3–10× faster | weeks |
| Cranelift JIT | IR → CLIF in-process | Apache-2.0 + LLVM exception | crate 0.137 | ours | ours | ours | no | 2–5× faster | weeks |
| LLVM (`inkwell`) | IR → LLVM IR | Apache-2.0 (+ LLVM's) | links LLVM 12–23 | ours | ours | ours | via Wasm output | 3–10× faster | weeks, heavy build |
| Wasm output | IR → Wasm (tail calls, maybe GC) | — | `wasmtime` 49 natively | ours | engine-limited | ours | yes | 2–5× faster | weeks |
| LuaJIT (`mlua`) | Lua text | MIT | crate; `nixpkgs#luajit` | none (doubles) | limited | coroutines | no | — | not a fit |
| JVM / Truffle / BEAM / GHC | — | — | large runtimes | — | — | — | no | — | not a fit |
| HVM / Bend | — | Apache-2.0/MIT | — | `Nat`, `U32`, `F32` | — | — | — | — | not a fit |

### Sources

- Marlow & Peyton Jones, "Making a fast curry: push/enter vs. eval/apply":
  https://www.microsoft.com/en-us/research/publication/make-fast-curry-pushenter-vs-evalapply/
- Leroy, "The ZINC experiment" (1990): https://xavierleroy.org/publi/ZINC.pdf
- Peyton Jones, the STG machine (1992): https://www.microsoft.com/en-us/research/?p=149862
- Ierusalimschy, de Figueiredo, Celes, "The implementation of Lua 5.0" (2005):
  https://www.lua.org/doc/jucs05.pdf
- Ullrich & de Moura, "Counting Immutable Beans" (2019): https://arxiv.org/abs/1908.05647
- Lean 4.30.0 release notes (LCNF): https://lean-lang.org/doc/reference/latest/releases/v4.30.0/
- Reinking, Xie, de Moura, Leijen, "Perceus" (PLDI 2021):
  https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/
- Xie & Leijen, "Generalized Evidence Passing for Effect Handlers" (ICFP 2021):
  https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf
- Sivaramakrishnan et al., "Retrofitting Effect Handlers onto OCaml" (PLDI 2021):
  https://arxiv.org/abs/2104.00250
- Effekt implementation notes: https://effekt-lang.org/docs/implementation
- Idris 2 backends: https://idris2.readthedocs.io/en/latest/backends/index.html, RefC:
  https://idris2.readthedocs.io/en/latest/backends/refc.html
- Agda compilers: https://agda.readthedocs.io/en/latest/tools/compilers.html
- Dafny reference: https://dafny.org/latest/DafnyRef/DafnyRef
- KaRaMeL: https://github.com/FStarLang/karamel
- Unison's Chez runtime: https://www.unison-lang.org/blog/jit-announce/
- Roc's move to Zig: https://rtfeldman.com/rust-to-zig
- Bend: https://github.com/bendlang/bend
- Malfunction: https://github.com/stedolan/malfunction
- Chez Scheme: https://github.com/cisco/ChezScheme; bignums:
  https://scheme.com/csug8/numeric.html
- Cranelift `cranelift-jit`: https://crates.io/crates/cranelift-jit; calling conventions:
  https://docs.wasmtime.dev/api/cranelift_codegen/isa/enum.CallConv.html
- inkwell: https://github.com/TheDan64/inkwell
- WebAssembly finished proposals:
  https://github.com/WebAssembly/proposals/blob/main/finished-proposals.md; browser support:
  https://web.dev/blog/wasmgc-wasm-tail-call-optimizations-baseline; Wasmtime defaults:
  https://docs.wasmtime.dev/api/wasmtime/struct.Config.html
- rquickjs: https://github.com/ryuapp/rquickjs (docs: https://docs.rs/crate/rquickjs/0.12.2)
- Boa 0.21: https://boajs.dev/blog/2025/10/22/boa-release-21
- `v8` crate build notes: https://docs.rs/crate/v8/152.0.0; size report:
  https://questions.deno.com/m/1204433075623428176
- QuickJS vs V8 on an M4 (third-party, indicative): https://github.com/buke/quickjs-go/wiki
- LuaJIT FFI integers: https://luajit.org/ext_ffi_semantics.html; `mlua`:
  https://github.com/mlua-rs/mlua
