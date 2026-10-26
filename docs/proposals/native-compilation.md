# Native compilation: how Stitchwort could run as machine code

**Status:** research and design note, 25 October 2026 (SW-477). Nothing here
changes the compiler. The experiments were scratch programs and aren't
committed; their code is described in [Appendix A](#appendix-a-the-experiments)
so they can be rewritten. Decisions are at the [end](#decisions) (D1250–D1253).
Matt has decided D1250–D1253. An external
reviewer read this note, and what changed is in
[External review](#external-review-25-october-2026).

Claims are marked like this:
- **[ran]**: measured for this note on an Apple M4 Pro, with
  `target/release/stitchwort` built from `main` on 25 October (the build the
  profile below used), Node 22.23.3, rustc 1.99 and clang 21, on a shared
  machine (load average 2–10, other lanes running). Times are the best or
  median of 2–3 runs.
- **[source]**: read in the code at `04790cb9`.
- **[inferred]**: my reasoning, not tested.
- **[unverified]**: a claim about another project I couldn't confirm in a
  source I opened.

Claims about other languages link to the source that was opened for this
note.

## 0. Summary

**The thesis.** N1–N5 build a native executor for decisions the machine
compiler already makes, not a new optimiser. The bytecode has fixed the
registers, moves, drops and reuse; the native code carries them out without
the interpreter's overhead. A new optimiser, or a new representation of
data, is a separate project that comes after this one works.

**The question.** How could Stitchwort be compiled to machine code for the
most speed, and what would it cost?

**Where we stand.** `stitchwort run` uses the bytecode machine of
`crates/rt` ([fast-runtime.md](fast-runtime.md)). On the `Set` benchmark
(a million inserts into a weight-balanced tree), it is about 2.7× slower than
`run --js` **[ran]**. Today's profile puts the cost in the machine itself
(dispatch, frames, registers, reference counts), not in the tree.

**The experiment** (§3). I translated the benchmark's hot path by hand into
Rust, keeping the machine's value layout, its reuse in place, its
overflow-checked numbers and its comparison through the instance
dictionary. That is roughly what a straightforward compiler from today's IR
would emit. It does the million inserts in **0.68 s**, against **8.7 s** on the
machine and **3.2 s** under Node **[ran]**:
- about **13× faster** than the machine, an optimistic upper bound for a
  real compiler;
- about **10×** with inlining turned off, which stands in for a simpler code
  generator;
- a version that also stores numbers unboxed in the nodes takes **0.12 s**,
  about 70× faster.

On bare calls, the machine spends about 37 ns per call and return. Native
code spends 0.6 ns, or 2.2 ns with the bookkeeping that stack safety and
resource limits need. These are upper bounds: a real compiler adds
overheads the hand translation skips (§3.4). So the claim is:
- **the target is at least 3×** over the machine (the N1 stop/go number);
- **4–8× is plausible** on call-heavy programs;
- **10–13× is the hand translation's optimistic upper bound** on this
  benchmark.

That is more than the 2–5× that [fast-runtime.md](fast-runtime.md) guessed.
Being faster than Node is not a success criterion: V8 can optimise a given
generated program very differently, so that comparison is less robust than
the one against the machine.

**How others do it** (§2):
- Lean 4 and Koka generate C, with reference counting and reuse in place.
- Idris 2 and Unison went through Chez Scheme. Unison's Chez runtime appears
  to have been shelved since **[secondary source]**.
- Roc and Effekt use LLVM. Roc is rewriting its compiler partly because of
  LLVM upgrades and Rust compile times.
- Agda and Rocq go through Haskell or OCaml.

Two features make Stitchwort unusually easy to compile:
- effects already keep their continuations on the heap, as data (D1162), so
  no backend needs to capture a stack;
- partial code is data (`Delay`) stepped by a runner loop, so tick counts
  live in Rust and don't depend on the backend.

**Recommendation** (§5):
1. **Compile to machine code with Cranelift, in-process, in the CLI**
   (`stitchwort run`), from the same optimised IR and bytecode the machine
   runs:
   - The compiled code calls the same Rust runtime: values, primitives,
     big numbers, freeing, the effect loop and the `Delay` runner.
   - It needs no C compiler or other tool at run time.
   - It keeps reference counting and reuse exactly as the machine decides
     them.
   - It counts frames and steps at each call (from N1), so that deep
     recursion reports `E-RESOURCE`. The counter defines the limit; a thread
     with a large reserved stack (N2) is only a safety margin behind it.
2. **The playground keeps the machine.** Cranelift can't run the code it
   makes inside a browser.
3. **Later, separately:**
   - storing numbers unboxed in data (a change of representation, worth
     about 5× more on this benchmark, and it helps the machine too);
   - possibly a C route, for a `stitchwort build` that writes a standalone
     executable.

About 8–10 lanes in all, each one stage, behind a `--native` flag until it
passes the differential tests (§6). N1 is a stop point: if it doesn't reach
3× with the counters in, stop and re-plan. The riskiest part of N1 is the
boundary between native code and the machine (§4.6).

**Not recommended:**
- LLVM: a heavy build and a version to keep up with.
- Generating Rust: rustc is far too slow to run on every `run`.
- Chez Scheme: it would lose reference counting and reuse, and it's an outside
  tool.
- Wasm as the main route: deep recursion and tail calls in browsers are not
  ready enough, and the gain over the machine in the browser is unmeasured.

## 1. Where the time goes today

### 1.1 The three runners

| Runner | What it is | Used by |
|---|---|---|
| Reference evaluator (`crates/core`) | The type checker's own evaluator; trusted, slow | `run --reference`, the oracle in differential tests, `eval`, the Tests tab |
| The machine (`crates/rt`) | Erased IR (`ir.rs`), simplified (`opt.rs`, `specialise.rs`, `fusion.rs`), compiled to register bytecode with moves and reuse tokens (`code.rs`), run by `machine.rs` with its frames on the heap | `stitchwort run`, `stitchwort test`, the playground's Run tab |
| JS backend (`crates/js`) | JavaScript from the checked terms (not from the rt IR), run by Node in a worker with a large stack | `run --js`, `extract` |

**[source]**: `crates/rt/src/lib.rs`, `crates/js/src/run.rs:1-30` (worker
thread "with a large stack, since generated code recurses on the JS stack").

### 1.2 The profile (25 October)

These come from the profile in the setperf scratch directory, made with
`stitchwort` built with a counting patch (`rt_prof.patch`) and macOS
`sample`. I re-ran the timings **[ran]**:

| Program (1,000,000 keys) | machine | `--js` |
|---|---:|---:|
| keys only (build and sum the list) | 0.35 s | 0.37 s |
| `Set.fromList` | 9.0–9.8 s | 3.5–3.8 s |
| so the inserts alone take about | **8.7 s** | **3.2 s** |

Per insert, the machine runs about 81 frames and 1,480 bytecode instructions
(`prof_set_nat_1M.txt`: 81,044,971 frames, 1,478,475,084 instructions for a
million inserts). `Std.Map.Tree.shape` alone is 776 million instructions,
about 40 per call. That works out at about 6 ns per bytecode instruction and
about 107 ns per frame.

Of the samples:
- 63% are in the machine's `run` loop itself;
- 11% are dropping values;
- 4% are growing the register vector at frame entry;
- 7% are allocation (`Rc::from_iter_exact` and mimalloc);
- most of the rest is primitives (`nat_add`, `nat_mul`).

The session's own analysis put about 19% of the time in the jump table
(instruction dispatch). It put the rest in frame push and pop, clearing
registers, and reference counting.

### 1.3 The call micro-benchmarks **[ran]**

`micro_call.sw` makes 20 million non-tail calls, 20 deep. `micro_tail.sw`
runs 20 million iterations of a tail-recursive loop. Checking takes about
0.09 s of each run.

| | machine | `--js` (incl. Node start) | Rust, plain | Rust, with frame and step counting |
|---|---:|---:|---:|---:|
| 20M non-tail calls | 0.83–0.94 s | 0.27–0.36 s | 0.012 s | 0.043 s |
| 20M tail iterations | 0.57–0.68 s | 0.27–0.33 s | 0.005 s | — |

So a call and return costs:
- about **37 ns** on the machine;
- under 10 ns under V8 (the run is mostly Node's start-up);
- **0.6 ns** as native code, or **2.2 ns** with the bookkeeping a safe
  backend needs (§4.3).

Calls are where an interpreter loses most, and this language makes a great
many small calls.

## 2. How comparable languages get native code

Every claim here links to a source I opened. The research was done by
reading papers, documentation and release notes; numbers are the authors'.

### 2.1 Lean 4: C, reference counting, reset/reuse

- **What it does:**
  - It compiles to C, then uses a bundled Clang (`leanc`, "a version of
    Clang") ([Ullrich & de Moura 2019, "Counting Immutable
    Beans"](https://arxiv.org/pdf/1908.05647);
    [Lean build tools](https://lean-lang.org/doc/reference/4.24.0/Build-Tools-and-Distribution/)).
    Toolchains are self-contained, so users don't install a C compiler.
  - Its IR, λRC, has explicit `inc`/`dec`, `reset`/`reuse` and inferred
    *borrowed* parameters (a parameter the callee doesn't own, so passing it
    costs no count).
  - "Recursive tail calls are implemented using gotos". Lean doesn't
    eliminate tail calls to a *different* function
    ([FP in Lean](https://lean-lang.org/functional_programming_in_lean/Programming___-Proving___-and-Performance/Tail-Recursion/)).
  - Big numbers used GMP in 2019. Whether they still do is **[unverified]**.
- **What it won:** on `const_fold`, "Lean is 5x as fast as OCaml". On the
  red-black map benchmark it beats everything except OCaml (same paper).
- **What it cost:** a whole new compiler. In v4.22 (August 2025), "the old
  compiler has been replaced by the new compiler"
  ([release notes](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)).
  Its new IR, LCNF, was "complete" only in v4.30 (May 2026)
  ([release notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/)).
  There, porting reset/reuse "prevents exponential code generation", and
  binaries shrank by about 15%.
- **Not found:** a published speedup of Lean's compiled code over its own
  interpreter.

### 2.2 Koka: C, Perceus, evidence passing

- **What it does:** Koka compiles to C11 "with no GC or runtime system". Its
  reference counting, Perceus, frees memory as soon as it's dead and reuses
  cells in place
  ([Perceus tech report](https://www.microsoft.com/en-us/research/uploads/prod/2020/11/perceus-tr-v1.pdf)).
  Stitchwort's machine already does a version of this (fast-runtime.md,
  stage 4).
- **What Perceus won:**
  - On the red-black tree benchmark, Koka is "within 10%" of C++'s
    `std::map`.
  - Koka without the reference-counting optimisations is "more than 2×
    slower".
  - Java used about 10× the memory.
- **Effect handlers** are compiled by *evidence passing*: the current
  handlers travel as a hidden argument.
  - Handlers that resume once, at the end ("tail-resumptive"), become plain
    calls, which "speeds up the counter benchmarks by 10×"
    ([Xie & Leijen 2021](https://www.microsoft.com/en-us/research/uploads/prod/2021/03/multip-tr-v4.pdf)).
  - Handlers that don't resume that way are about 5× slower than OCaml 5.
- **Wasm:** Koka reaches wasm through Emscripten on the C backend
  ([Koka README](https://github.com/koka-lang/koka)).
- **In-place updates:** FP² ("fully in-place" functions) are guaranteed to
  run without allocating
  ([paper](https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fbip.pdf)).

### 2.3 Idris 2: Chez Scheme by default; RefC experimental

- **Backends:** "By default, Idris compiles to executables via Chez Scheme".
  Racket, Gambit, JavaScript and RefC are the alternatives
  ([backends](https://idris2.readthedocs.io/en/latest/backends/index.html)).
- **Chez needs installing:** "to run Idris programs you will need to install
  Chez Scheme". The output is a shell script plus compiled Scheme, and a
  standalone binary needs a separate tool
  ([Chez backend](https://idris2.readthedocs.io/en/latest/backends/chez.html)).
- **RefC** (C with reference counting) is labelled experimental. It is
  slower than the Scheme backends because its counting "hasn't been
  optimized yet"
  ([RefC](https://idris2.readthedocs.io/en/latest/backends/refc.html)).
- **No published numbers** compare the backends.

### 2.4 Agda and Rocq: through another functional language

- **Agda's MAlonzo** translates to Haskell and calls GHC
  ([Agda compilers](https://agda.readthedocs.io/en/latest/tools/compilers.html)).
  - Its unsafe coercions have hit a GHC optimiser bug
    ([GHC #17206](https://gitlab.haskell.org/ghc/ghc/issues/17206)).
  - GHC's optimisation flags add 30–40% to compile time for MAlonzo output
    ([2026 paper](https://arxiv.org/pdf/2603.24199)).
- **Rocq** extracts to OCaml with `Obj.magic` where the code isn't ML-typable
  ([extraction](https://rocq-prover.org/doc/v9.3/refman/addendum/extraction.html)).
  Its `native_compute` (convert to OCaml, compile, run) is "typically two to
  five times faster than vm_compute" (its bytecode machine). It has
  "considerably more overhead", so it's recommended only for runs of 5–10 s
  or more
  ([Rocq manual](https://rocq-prover.org/doc/V9.0.0/refman/proofs/writing-proofs/equality.html)).
- **The lesson for us:** going through another typed language means fighting
  its type system with coercions. Its compile time is paid on every run.

### 2.5 Roc: LLVM, plus a fast "dev" backend

- **Backends:** the Rust-era compiler had three: LLVM "for fastest possible
  execution speed", a dev backend that wrote object files directly "for fast
  builds", and a wasm backend
  ([repository mirror](https://git.joshthomas.dev/language-servers/roc/src/branch/main/crates/compiler/gen_dev)).
- **The rewrite:** Roc is being rewritten in Zig. Richard Feldman wrote that
  "the LLVM upgrade process has been very time-consuming" and that Rust's
  compile times are slow. The new plan includes an interpreter to skip code
  generation in development
  ([Feldman's gist](https://gist.github.com/rtfeldman/77fb430ee57b42f5f2ca973a3992532f)).
- **Memory:** Roc uses Perceus-style reference counting with in-place
  mutation **[secondary source]**.

### 2.6 Unison: Chez Scheme from an interpreter

- **The 2022 result:** in 2022 Unison announced code compiled through Chez
  that ran "470x faster" than its Haskell interpreter. That was on one
  arithmetic loop, without abilities (effects) or continuations yet
  ([announcement](https://unison-lang.org/blog/jit-announce/)).
- **Today:**
  - The current docs describe `compile` producing a file that the
    interpreter runs
    ([docs](https://www.unison-lang.org/docs/ucm-commands/compile/)).
  - A comment attributed to the Unison team says the Chez work was "put …
    on ice" **[secondary source, not opened]**.
- **Lesson:** a speedup on a toy loop doesn't survive contact with effects
  and the rest of the language unless the runtime is designed for them.

### 2.7 Effekt: LLVM with reference counting and one-shot continuations

- **The ICFP 2025 backend:** it emits LLVM with "garbage-free reference
  counting". Capturing and resuming a continuation takes constant time when
  it is resumed once
  ([Müller et al. 2025](https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf)).
- **Speed:** its geometric mean is 2.2× faster than OCaml 5.1.1 and 10.2×
  faster than Koka 3.1.2 on its effect benchmarks.
- **Cost:** its custom calling convention and stack management are things
  "LLVM is not able to optimize" (its Fibonacci benchmark is slow).
- **History:** the LLVM backend replaced an MLton one that was faster
  ([Effekt evolution](https://effekt-lang.org/evolution)).

### 2.8 OCaml 5: effects in a native compiler

From the PLDI 2021 paper "Retrofitting effect handlers onto OCaml"
([Sivaramakrishnan et al.](https://arxiv.org/abs/2104.00250)):
- **Continuations are one-shot**: resuming one twice raises
  `Invalid_argument`.
- **Fibers live on the C heap.** Each handled computation runs on its own
  small stack (a *fiber*), allocated with `malloc`.
  - A fiber starts at 16 words and is copied to an area twice the size when
    it overflows.
  - A cache of freed stacks keeps this cheap.
  - Function prologues check for stack overflow.
- **Cost to programs that don't use effects:** under 1% on average (8 of 54
  programs above 10%), and code is 19% larger.
- **Effects versus alternatives:** a generator written with effects is
  2.76× slower than hand-written CPS, and a monadic one is 8.69× slower.

The lesson is that a native compiler needed a new stack discipline to get
cheap one-shot continuations. Stitchwort's heap continuations (§4.1) avoid
that, at the cost of allocating a cell per pending `bind`.

### 2.9 What this says

- **Two working patterns** (my reading, from the sources above):
  1. Reuse a mature runtime: Chez (Idris, the old Unison plan), GHC (Agda) or
     OCaml (Rocq). You get bignums, tail calls and deep stacks for free, and
     you lose control of memory: no reference counting, no reuse.
  2. Generate C or LLVM with your own reference-counted runtime (Lean, Koka,
     Roc, Effekt). It's fastest, and it's where Perceus's gains come from.
     But it's the most work, and every one of these projects has rewritten
     its backend at least once.
- **No mature production functional language uses Cranelift as its primary
  backend.** None of the projects above does. Haskelujah, a Haskell compiler,
  has a Cranelift backend with closures, thunks, tagged constructors and
  pattern matching
  ([docs.rs](https://docs.rs/haskelujah-backend-cranelift/latest/haskelujah_backend_cranelift/),
  version 0.1.1, opened for this note). It is early work, so it isn't strong
  prior art, but it means "nobody does" would be too strong. This is a gap in
  prior art, not evidence against Cranelift. Cranelift is used for Wasm and for Rust debug builds (§2.10).
- **Effects are the hard part elsewhere:**
  - OCaml 5 needed segmented stacks.
  - Effekt needed a custom calling convention.
  - Koka needed evidence passing.

  Stitchwort mostly sidesteps this, because its continuations are already
  heap data (§4.1).

### 2.10 Code generators from Rust

**Cranelift**
- **What it is:** the code generator of Wasmtime and of Rust's alternative
  debug backend.
- **Version and licence:** `cranelift-codegen` 0.137.0 (20 October 2026),
  Apache-2.0 with the LLVM exception
  ([crates.io](https://crates.io/api/v1/crates/cranelift-codegen)).
- **Targets:** x86-64, aarch64, s390x and riscv64. It doesn't emit wasm
  ([Pulley docs](https://docs.wasmtime.dev/examples-pulley.html)).
- **Code quality:** its README cites a third-party measurement of its code
  at "~2% slower than V8 (TurboFan), ~14% slower than WAVM (LLVM)". It
  compiles about an order of magnitude faster than LLVM
  ([README](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/README.md)).
- **Rust's Cranelift backend:** it speeds up whole debug builds by about
  10–15% on average
  ([Rust project goal, 2026](https://goals.rust-lang.org/2026/improve-cg_clif-performance.html)).
  That is a measure of compile time, diluted by the rest of rustc.
- **Tail calls:** a `tail` calling convention was added in 2023. Wasmtime
  waited for it to be as fast as the default before using it
  ([Bytecode Alliance, 2023](https://bytecodealliance.org/articles/wasmtime-and-cranelift-in-2023)).
  Wasmtime has had wasm tail calls on by default since version 22
  ([wasm features](https://webassembly.org/features.json)).
- **macOS arm64:**
  - `cranelift-jit` maps its code memory with an ordinary anonymous mapping,
    without `MAP_JIT`. The research agent checked this in the source.
  - A contributor (bjorn3) says the kernel enforces write-xor-execute "only
    when hardened runtime is enabled", and that `MAP_JIT` isn't needed
    otherwise
    ([wasmtime#12076](https://github.com/bytecodealliance/wasmtime/issues/12076),
    opened for this note). The issue itself was closed as a duplicate of
    #11989, which I didn't open, so its outcome is unknown to me.
  - The wasmer-sdk Swift README says "the pinned Cranelift runtime maps
    generated code without `MAP_JIT`", so an app with Hardened Runtime needs
    the entitlement `com.apple.security.cs.allow-unsigned-executable-memory`,
    and `allow-jit` alone doesn't cover it
    ([README](https://github.com/wasmerio/wasmer-sdk/blob/main/swift/README.md),
    opened for this note). It also says Cranelift is a problem on iOS, which
    forbids runtime code generation. We don't target iOS.
  - So a plain CLI should work, but a signed or hardened build may need an
    entitlement or `MAP_JIT`. Stage N0 must check each case (§6).
  - Writing object files instead has an open arm64 Darwin relocation bug
    ([wasmtime#4564](https://github.com/bytecodealliance/wasmtime/issues/4564)).
    That's a reason to JIT rather than write `.o` files.
- **In wasm:** the research agent built `cranelift-codegen` 0.137 for
  `wasm32-unknown-unknown` and ran it under Node. It compiled a
  tail-convention function to aarch64 machine code in about 16 ms, from a
  4.2 MB `.wasm` (unstripped) **[ran by the research agent]**. So it *runs*
  in a browser, but a page can't execute the machine code it produces.
- **Inlining:** whether it inlines, and how much, is **[unverified]**. The
  experiment's no-inlining row stands in for "less inlining than LLVM".

**LLVM from Rust**
- **Bindings:** `inkwell` supports LLVM 12–23 by Cargo feature and needs an
  installed LLVM ([inkwell](https://github.com/TheDan64/inkwell)).
  `llvm-sys` 231 needs `llvm-config`
  ([docs.rs](https://docs.rs/crate/llvm-sys/latest)).
- **Tail calls:** a `musttail` call "must be tail call optimized", and
  `tailcc` guarantees tail calls
  ([LangRef](https://llvm.org/docs/LangRef.html)).
- **Not found:** link time and binary size numbers **[unverified]**.

**C**
- **Guaranteed tail calls:**
  - clang has `musttail`, and GCC 15 added a `musttail` attribute
    ([GCC 15 changes](https://gcc.gnu.org/gcc-15/changes.html)).
  - Lean only turns direct self tail calls into loops (§2.1).
  - A code search for `musttail` in Koka found nothing; its C backend turns
    self-calls into loops ([koka](https://github.com/koka-lang/koka)).
- **Fast compilers:** tcc compiles about 9× faster than old GCC at `-O0`
  ([tcc](https://bellard.org/tcc/)), but makes slower code, and Bellard no
  longer works on it.
- **C to wasm:** clang compiles C to wasm without Emscripten
  ([Surma](https://surma.dev/things/c-to-webassembly/)). `musttail` there
  needs `-mtail-call` (tested by the research agent with clang 21).

**Wasm**
- **What browsers support** (from [webassembly.org/features.json](https://webassembly.org/features.json)):

  | Feature | Chrome | Firefox | Safari | Wasmtime |
  |---|---|---|---|---|
  | Tail calls | 112 | 121 | 18.2 | 22 |
  | Exceptions (exnref) | 137 | 131 | 18.4 | 47 |
  | Stack switching | flag only | – | – | – |

- **Stack switching** (which would give deep recursion and continuations
  in wasm) is at phase 3
  ([proposals](https://github.com/WebAssembly/proposals)) and
  work-in-progress in Wasmtime
  ([Wasmtime proposals](https://raw.githubusercontent.com/bytecodealliance/wasmtime/main/docs/stability-wasm-proposals.md)).
- **Wasm_of_ocaml** still defaults to a CPS transform for effects because
  stable browsers lack it
  ([OCaml, April 2026](https://ocaml.org/backstage/2026-04-16-wasm-of-ocaml-what-changed-since-6-1)).
- **Wasmtime's size:** the default build is 19 MB; 2.1 MB without its
  compiler ([Wasmtime minimal](https://docs.wasmtime.dev/examples-minimal.html)).
- **Speed:** wasm ran 45–55% slower than native in browsers in 2019
  ([Jangda et al.](https://www.usenix.org/conference/atc19/presentation/jangda)).
  Newer measurements of about 1.3× slower were seen only in search excerpts
  **[unverified]**.

**Chez Scheme**
- **Licence and packaging:** Apache-2.0, runs on AArch64 macOS
  ([ChezScheme](https://github.com/cisco/ChezScheme)). nixpkgs has `chez`
  10.4.1 (checked with `nix search` by the research agent).
- **Continuations:** `call/1cc` makes one-shot continuations on segmented
  stacks ([Chez user guide](https://scheme.com/csug8/control.html)).
- **Speed:** Racket on Chez runs at "about the same" speed as old Racket,
  with much cheaper continuations
  ([Racket blog](https://blog.racket-lang.org/2020/02/racket-on-chez-status.html)).
- **Not verified:** Chez against C speed, and its bignums and tail calls
  (which the Scheme standard requires).

**Interpreter techniques** (for route (a))
- **Threaded dispatch:** a C protobuf parser with `musttail`-threaded
  dispatch reached "more than double" the previous state of the art. Its
  author warns that "'tail calls == 2x speedup' is the wrong message"
  ([Haberman](https://blog.reverberate.org/2021/04/21/musttail-efficient-interpreters.html)).
- **CPython 3.14's tail-calling interpreter:** about 1–5% faster, once a
  compiler regression is accounted for
  ([Elhage](https://blog.nelhage.com/post/cpython-tail-call/)).
- **Rust's `become`** (guaranteed tail calls, which an interpreter needs for
  this) is unstable
  ([rust#112788](https://github.com/rust-lang/rust/issues/112788)), with
  stabilisation "hopefully in 2027"
  ([Trifecta](https://trifectatech.org/blog/tail-calls-project-goal/)).
- **Keeter's Rust interpreter** using it (on nightly):
  - natively, 1.5–2× faster than a `match` loop;
  - compiled to wasm, **1.2–4.6× slower** than the `match` loop
  ([Keeter, 2026](https://www.mattkeeter.com/blog/2026-04-05-tailcall/)).

  So threaded dispatch would help the CLI and hurt the playground.
- **Superinstructions:** up to 3.17× over threaded code in Forth-style
  interpreters ([Ertl & Gregg 2003](https://www.eecg.utoronto.ca/~steffan/carg/readings/optimizing-indirect-branch-prediction.pdf)).
- **Register machines:** Lua 5's register machine was more than twice as fast
  as Lua 4's stack machine on a loop ([Lua 5](https://www.lua.org/doc/jucs05.pdf)).
- **Wasm3,** a fast tail-calling interpreter, is 4–15× slower than compiled
  C ([wasm3](https://github.com/wasm3/wasm3/blob/main/docs/Interpreter.md)).

  That is a fair guess at how close any interpreter, including ours, can
  get to native code.

## 3. The experiment: the `Set` insert by hand

### 3.1 What was translated

These are the functions that take 98% of the profile:
- `Std.Map.Tree.insertWith.%match1[0]` (the insert, specialised);
- `shape`;
- `rebuild`;
- `singleL`/`singleR`/`doubleL`/`doubleR`;
- `Nat.compare`.

They were translated from the IR listing (`set_nat.ir`) into Rust, in three
versions (Appendix A):

1. **uniform**: what a compiler from today's IR would emit.
   - Every value is the machine's three-word `Value`: a small `Nat` inline,
     a constructor as a tag plus `Rc<[Value]>`.
   - `Nat` arithmetic is overflow-checked, with a big-number escape.
   - The comparison is an indirect call through the instance dictionary that
     returns an `Ordering` value, as the IR's `apply` does.
   - A node that is uniquely owned is taken apart and refilled in place, as
     `Unpack`/`CtorReuse` do.
   - Recursion is on the Rust stack, with no frame or step counting.
2. **uniform, no inlining**: the same code with every helper marked
   `#[inline(never)]`. This stands in for a code generator that inlines
   less than LLVM. How much Cranelift inlines is **[unverified]** (§2.10).
3. **typed**: a node is a struct with `u64` size and key and the unit value
   erased. This is what a compiler that also chose representations by type
   would emit.

The machine and Node run the real program, `set_nat_1000000.sw`:
`Set.size (Set.fromList keys)` over the keys `(i * 7919) % 1000000`.

### 3.2 Results **[ran]**

The inserts only, for a million keys. Each answer is 1,000,000.

| Runner | Inserts | vs machine | vs Node |
|---|---:|---:|---:|
| machine (`stitchwort run`) | 8.7 s | 1× | 0.37× |
| Node (`run --js`) | 3.2 s | 2.7× | 1× |
| Rust, uniform, no inlining | 0.79–0.87 s | ~10× | ~3.8× |
| Rust, uniform | 0.67–0.72 s | ~13× | ~4.7× |
| Rust, typed | 0.12 s | ~70× | ~27× |

The machine and Node times are whole runs minus the keys-only run (§1.2).
The Rust times are measured around the insert loop. The allocator is
mimalloc in each case. With the system allocator, uniform was 0.59 s (one
run).

**Correction (D1261):** "uniform" reuses a node's cell at every level, which
today's IR doesn't do. A variant doing the IR's allocations takes 1.8–2.0 s
(see "The miss investigated", under N1 as built).

### 3.3 What it shows

- **Execution through the interpreter is the dominant avoidable cost on this
  workload.** The same memory layout, the same counts and the same reuse,
  run as machine code, are 10–13× faster. (This removes dispatch, register
  access, call and return and frame handling together; dispatch alone is
  only about 19% of the profile, §1.2.) That matches the call micro-benchmark (§1.3): about
  37 ns per call on the machine against 1–2 ns natively.
- **The value layout is the next factor after that.** Typed nodes are
  another 5–6× faster than uniform ones:
  - a node is 48 bytes instead of 136;
  - a size or key read is a load, not a tag check and a copy;
  - there's no `Ordering` value.

  That is a separate project from native code. It would help the machine too
  (less memory traffic), though its main gain needs a compiler.
- **Inlining matters less than expected** (0.68 s against 0.83 s). The IR's
  simplifier (`opt.rs`) already inlines small functions, so a code
  generator that doesn't inline loses little.

### 3.4 Why the real gain would be smaller **[inferred]**

The hand translation skips things a real backend must do:

1. **Frame and step counting** (§4.3): each call counts against the frame
   and step limits. On the bare-call benchmark that took a call from 0.6 ns
   to 2.2 ns. On the `Set` code, which does real work per call, it should be
   a much smaller share.
2. **Code quality:** Cranelift's code is somewhat slower than LLVM's, which
   compiled the experiment (§2.10).
3. **Generality:** the hand translation knows `Shape` is a tag and that
   `shape`'s result is matched at once. A compiler from the bytecode would
   materialise a `Value::Tag` and switch on it. That's cheap, but not free.

**Claim for a Cranelift backend on today's representation [inferred]:**
- **target: at least 3×** faster than the machine on this benchmark;
- **plausible: 4–8×** on call-heavy programs;
- **the hand translation's 10–13×** is an optimistic upper bound, not a
  forecast.

The evidence shows there is headroom for a several-fold gain. It doesn't
separate 3×, 5× and 8× well, and 4× must not later be read as a failure.
Speed against Node isn't a criterion. Stage N1 measures the real number (§6).

## 4. What maps onto machine code, and how

### 4.1 Effects and handlers

**[source]**: `crates/rt/src/effect.rs:1-33`, effect-runtime.md §9 (D1162).

- **What the machine does:** it runs effects with four natives that replace
  the library's `bind`, `foldComp`, `translate` and `runPure`.
  - `bind` on a finished computation calls the continuation. Otherwise it
    builds a `Bind` node and calls nothing.
  - One loop runs a computation for a handler. It keeps the pending
    continuations on a persistent linked list in the heap.
  - **Capturing a continuation is keeping a pointer** to that list. Resuming
    is applying closures.
- **Native code needs:**
  - **No stack capture:** no fibers, no segmented stacks, no `setjmp`, no
    CPS. OCaml 5 and Effekt had to build machinery for exactly this (§2.7,
    §2.8).
  - **Closures and indirect calls.** Every backend has those.
  - **The effect loop** stays Rust code in the runtime and calls compiled
    closures.
  - **The specialisations** (`fusion.rs`'s state loops, `specialise.rs`'s
    empty-row variants) happen in the IR, before any backend, so a native
    backend gets them for free.

One thing changes **[inferred]**:
- On the machine, the loop runs on the machine's frames (`Ret::Eff`), so
  nothing nests in Rust.
- In native code, a continuation the loop calls runs on the native stack.
  Its own calls nest there like any other calls, and that is bounded by
  §4.3's limit.
- `bind (Done x) k` calling `k` directly is "an explicit invariant of this
  backend" on the machine (effect.rs). Natively it costs native stack, as
  non-tail recursion does. It needs the same depth check, and a test that a
  long effectful `List.map` still runs.

### 4.2 Partial code and ticks

**[source]**: `crates/rt/src/run.rs:1-40, 216-250`; partial.md §7.4.

- A partial `main` is a `Delay` value. Only the runner (`run.rs`) looks
  inside it, and **each recursive partial call is exactly one tick**, by the
  runner's equations.
- A native backend builds the same `Delay` data by calling the same runtime
  constructors, and the same Rust runner steps it.
- So **tick counts are identical by construction**, provided the compiled
  code builds the same `Delay` values. The existing tick-limit tests
  (`run_main_with`, `max_ticks`) check that.

### 4.3 Stack safety and resource limits

This is the main design question for any native backend:
- The machine keeps frames on the heap, so a million-deep recursion is fine
  and running out of frames is a clean `E-RESOURCE`.
- Native code wants the machine stack, because that's where its speed
  comes from (§1.3).

**[source]** for each of the following:
- The JS backend already runs generated code on the native (V8) stack, in
  a worker with a large stack (`crates/js/src/run.rs:9-11, 707-717`).
- The CLI already runs the compiler on a 64 MiB thread
  (`crates/cli/src/main.rs:233`), using `driver::with_stack`.
- The machine counts each frame entered as a step against `Limits::steps`,
  and the frames pending against `Limits::frames` (2,000,000)
  (`machine.rs:19-21, 36-41`).

The design **[inferred]**:
- **The frame counter defines the limit. The reserved stack is only a
  safety margin behind it.** Run compiled code on its own thread with a
  large reserved stack (N2). On 64-bit systems that is address space, not
  memory, until it's touched.
  - **Don't size it as the frame limit times the largest Stitchwort frame.**
    Native frame sizes depend on Cranelift, the ABI, spills and prologues,
    and may change with a version, so that product is not a safe bound.
  - **Pick a generous size** (about 1 GiB is a starting point, not a
    semantic fact) **and test that the counter always fires first** on each
    supported target: a deep non-tail recursion, with the largest frames the
    test programs can make, must end in `E-RESOURCE` and never in a crash.
    The size is not part of the language's meaning.
  - If the margin turns out awkward, a stack-limit probe is the alternative
    (below).
- **Count at each call, exactly as the machine does** (from N1, so that the
  stop/go speed includes it; the big stack and the full `E-RESOURCE`
  handling follow in N2): increment the steps
  and frames, compare them with their limits, and leave on a cold path with
  `E-RESOURCE`. Measured on the bare-call benchmark, that is 2.2 ns per call
  instead of 0.6 (§1.3). It is still 17× cheaper than the machine's call.
- **If the counts are the same ones**, native code runs out at *exactly*
  the same points as the machine. That is better than today's machine
  against the reference evaluator, which run out at different points
  (fast-runtime.md, stage 3).
- **A cheaper alternative**, if the counting shows up in profiles: compare
  the stack pointer with a limit, as Go and Rust's stack probes do. Running
  out then happens at a point that depends on frame sizes, which is still
  reported the same way.
- **Tail calls must not grow the stack.**
  - Self tail calls become loops in any backend.
  - Calls to *another* function in tail position need a real tail call.
    Lean doesn't have them (§2.1); Cranelift does (§2.10); C has them only
    with clang's `musttail` (§2.10).
  - Stitchwort needs them: the machine guarantees "a 3,000,000-step tail
    loop within 100 frames" (fast-runtime.md, stage 2), and mutually
    recursive state machines depend on it.

### 4.4 Big numbers, text, pattern matching

- **`Nat` and `Int`:**
  - The fast path is a 64-bit operation plus an overflow check, emitted
    inline. That's what the experiment did.
  - The slow path calls `prims.rs`, which already defines exactly what the
    reference evaluator computes (fast-runtime.md, stage 2).
  - Rust keeps `num-bigint`; nothing new.
- **`Text`** and the text natives: calls into the runtime.
- **Pattern matching:** the bytecode's `Switch` is a jump table on the tag.
  It maps directly onto a jump table in machine code. `NumSwitch`, `Test`
  and `NatCase` become compares and branches.

### 4.5 Reference counting and reuse

- **The decisions are made before code generation.** `code.rs` decides
  where a value moves, where it's dropped, and which emptied cell a new
  constructor reuses. It writes those decisions into the bytecode
  (`MOVE`, `Drop`, `Unpack`, `CtorReuse`, `DropReuse`) **[source]**.
- **A backend translating that bytecode inherits them unchanged.** So
  memory behaviour, including the in-place reuse that made the merge sort
  2.8× faster, stays the same.
- **What machine code adds:**
  - It inlines the increment and the "is this the last reference?" test.
  - It calls the runtime's freeing code (the work list that never recurses)
    only when a count reaches zero.
- **Later:** Lean's *borrowed parameters* (§2.1) would remove many counts.
  That's an IR change, useful to both runners.

### 4.6 The native/machine boundary (the biggest N1 risk)

N1 translates only some instructions, and some functions will have
instructions it doesn't handle. That looks like scaffolding but it is the
hardest part of N1, because the machine isn't a recursive interpreter that
native code can simply call. **[source]** for each fact below, in
`crates/rt/src/machine.rs` unless noted:
- **Frames are heap data.** `State` holds `regs: Vec<Value>` and
  `frames: Vec<Frame>` (`:107-127`). A `Frame` is a code index, a pc, a base
  into the shared register vector, the closure's `env`, and a `Ret`. There
  is no Rust recursion for a Stitchwort call: `Instr::Call` pushes a
  `Frame` and does `continue 'outer` (`:965-985`).
- **A frame's continuation is not always a register.** `Ret` (`:61-100`) can
  be a register of the caller, the host, a constant's cache, the rest of an
  over-application (`Apply`), a `Text.fold` step, an effect loop (`Eff`), and
  so on. A native callee returning into one of those needs the machine's
  `run` loop to do the delivery.
- **Arguments are moved.** `get!` takes a register's value with
  `mem::take` when the operand is marked `MOVE`, otherwise clones it
  (`:918`); `Call` and `TailCall` do this into the new frame or
  into `scratch`.
- **Counting is in `State`.** `enter_frame` (`:257`) bumps `steps` and checks
  `frames.len()` against `Limits::frames`; `replace` (`:296`, the tail call) bumps
  `steps` only.
- **Errors drop everything.** On `Err`, `Machine::finish` clears `frames`,
  `regs` and `scratch` (`:230-241`), which releases every owned value.
- **The host already re-enters.** `Machine::call(f, args)` (`:223`) starts a
  fresh `run` for a callback, and the partial-code runner in `run.rs` calls
  it for each continuation (`run.rs:254, 297, 322, 336, 370`). Values are
  `Rc` (`value.rs`), so the machine and all native code in one run must stay
  on one thread.

The reviewer's ten questions, answered for the design recommended below
(a design choice, **[inferred]**):

| Question | Answer |
|---|---|
| Can native code call interpreted code? | Not within a run. See the recommendation. |
| Can interpreted code call native code? | Only at the start: the entry point of a run is native or it isn't. |
| Can it bounce repeatedly? | No: a run is wholly native or wholly machine. |
| Who owns arguments across a transition? | As `Call` does: operands marked `MOVE` are moved, others cloned, and the callee owns what it receives. At the entry, the host's `Vec<Value>` is moved in. |
| Are machine and native frames counted identically? | With no mixing there is one counter in a run. The native one follows the machine's rules: `enter_frame` on a call, `steps` only on a tail call. |
| Tail call across the boundary? | Cannot occur, because there is no boundary inside a run. A tail call to a function outside the subset makes the whole run machine. |
| Drops and reuse at the boundary? | None to define. Inside native code, drops and reuse are the bytecode's (`MOVE`, `Drop`, `Unpack`, `CtorReuse`). |
| Can an interpreted callee invoke a native callback? | No: no machine frames exist in a native run. |
| Which stack does the interpreter run on? | The machine keeps its frames on the heap and runs on whatever thread starts it. A native run uses the big-stack thread (N2). |
| Can native code leave on an error without leaks? | Each native frame owns its registers and drops them as it returns a `Result::Err` up the call chain (a panic is not an exit route). N1 tests this with the allocation trace (§6). |

**Two ways to mix:**
1. **Per-function mixing.** Any function may be native or machine, and
   control crosses at any `Call`.
   - Native to machine needs a nested `run` on the Rust stack, which defeats
     the heap frames: machine to native to machine nests without bound, and
     the machine's `Ret` kinds (`Apply`, `Fold`, `Eff`) have no native
     counterparts.
   - Machine to native needs a native entry point per function, and a way
     for the machine's loop to resume after a native callee returns.
   - Counting, `MOVE` ownership, errors and tail calls would each need a
     rule at the crossing.
2. **Whole reachable islands.** An entry point (`main`, a test, a
   `Machine::call` target) is native only if everything it can reach is in
   the N1 subset. Otherwise that whole invocation runs on the machine, as
   today.
   - There are no crossings inside a run, so none of the ten questions has
     a hard answer.
   - Reachability is a static walk over `Call`, `TailCall`, `Global` and
     `Pap` edges in the bytecode. Indirect calls (`Apply`) are the catch:
     N1 either rejects any function that applies an unknown value (the
     subset has no closures until N3) or counts every lambda as reached.
   - It costs coverage early: one unsupported instruction anywhere
     reachable makes the run wholly machine. N1's benchmarks
     (`micro_call`, `micro_tail`, `Set`) are chosen to be inside the subset.

**Recommendation: whole reachable islands for N1 to N3.** It keeps the
first backend boring and the differential tests meaningful, and it matches
the thesis (§0). The machine stays the fallback for a whole run.
Per-function mixing is worth designing only if N3's coverage turns out too
low, and then as its own stage. Once the subset is complete the question
goes away. (The effect loop and `Text.fold` are Rust code that calls back
into compiled closures from N4; that is a native-to-runtime call, not a
mix with machine frames, and §4.1 covers it.)

## 5. The routes

Each route is judged on:
- speed;
- effects, stack safety and tail calls;
- what users need installed;
- the playground;
- risk and size.

"Lanes" are stage-sized tasks as the board uses them.

### (a) A faster interpreter (the baseline)

- **What:** keep the machine and make it cheaper per instruction.
  - Smaller frames and no register clearing on entry: the profile's
    `Vec::resize` and teardown.
  - Superinstructions for the frequent pairs (`Switch→Unpack`,
    `CtorReuse→Return`, `Field` of a size).
  - A 16-byte `Value`.
  - Threaded dispatch with tail calls between handlers, if Rust's
    `become` is usable (§2.10).
- **Speed:**
  - Dispatch is about 19% of the time, so removing it entirely gains at most
    1.25×.
  - Frames and registers are a larger share, but no interpreter gets near
    1–2 ns per call.
  - My estimate is **1.3–2×** **[inferred]**. Published results for
    tail-call threading are in §2.10: 1.5–2× natively for one Rust
    interpreter, but it needs nightly Rust.
- **Everything else:** unchanged (it's the machine).
- **Playground:** it gains from the frame, register and superinstruction
  work. This is the only route that speeds the playground up without new
  browser features.
  - Threaded dispatch is the exception: one Rust interpreter ran 1.2–4.6×
    *slower* in wasm with it (§2.10).
  - So that part would be native-only, behind a Cargo feature.
- **Risk:** low. **Size:** 2–3 lanes.
- **Verdict:** worth doing for the playground and `test`, but it can't reach
  Node, let alone native code.

### (b) Generate C, call a C compiler

- **What:** IR or bytecode to C text, compiled by `cc` against a runtime.
- **Speed:** best-in-class code (LLVM or GCC). On the experiment, the
  uniform row, about 13× **[ran, as an upper bound]**.
- **Effects, ticks, big numbers:** as in §4. Effects need closures only.
- **Tail calls:** C doesn't guarantee them.
  - clang's `musttail` does, and so does GCC 15 (§2.10).
  - Otherwise you need a trampoline, which slows every tail call.
  - Koka and Lean live with self-tail-calls-only plus their own tricks.
- **Runtime:** the Rust runtime would need a C interface. The 3-word `Value`
  would need a `#[repr(C)]` layout, or a second runtime written in C, as
  Lean and Koka have.
- **Tools:**
  - **Needs a C compiler on the user's machine at run time.** Nix provides
    one; plain users may not have one.
  - Compile latency is clang's: a second or more for a large program at
    `-O2` **[inferred]**. That's fine for `build`, and noticeable for `run`
    (results could be cached by content hash).
- **Playground:** none directly. The same C could be compiled to wasm with
  clang ahead of time, but not in the browser.
- **Risk:** medium. Two runtimes, or a C ABI over Rust's; two compilers'
  quirks. **Size:** 8–12 lanes.
- **Verdict:** the best route to a standalone executable
  (`stitchwort build`) later. For `run`, it is worse than (c).

### (c) Cranelift, in-process (recommended)

- **What:** translate each function's bytecode (or IR) into Cranelift IR
  in the CLI, compile it to machine code in memory, and call it.
  - The compiled code calls the same Rust runtime through function
    pointers: `prims.rs`, `value.rs`'s freeing, the effect loop, the
    `Delay` runner and `Text.fold`.
  - Unsupported corners can call back into the runtime.
- **Speed:** about 10× on the experiment without inlining, an upper bound.
  Target at least 3×, plausibly 4–8× in practice (§3.4).
- **Effects, ticks, big numbers, reference counting:** as in §4. The code
  generator is the only new part; every runtime service is shared with the
  machine.
- **Tail calls:** Cranelift has a `tail` calling convention and
  `return_call` (§2.10).
- **Tools:**
  - **Nothing at run time**: Cranelift is a Rust library, Apache-2.0 with the
    LLVM exception (§2.10).
  - The CLI grows by some megabytes. Cranelift built to wasm was 4.2 MB
    unstripped (§2.10). The native size is for stage N0 to measure.
  - Nix: ordinary crates; nothing to install.
- **Compile latency:** Cranelift was built to be fast (§2.10). A program
  plus the part of std it reaches is hundreds of small functions
  **[inferred]**.
- **Playground:** unchanged. Cranelift is left out of the wasm build by a
  Cargo feature. The playground keeps the machine; even if Cranelift ran in
  wasm, the browser can't execute the machine code it makes.
- **macOS:**
  - `cranelift-jit` works on Apple Silicon for an ordinary CLI.
  - A hardened-runtime (signed) build would need `MAP_JIT` memory, which
    `cranelift-jit` doesn't use (§2.10).
  - Writing `.o` files instead has an open arm64 macOS bug, so JIT it is.
- **Risk:** medium.
  - New ground: no mature production functional language uses Cranelift as
    its primary backend (§2.9).
  - The native/machine boundary is the biggest implementation risk (§4.6).
  - A miscompile gives wrong output, which the differential tests are built
    to catch.
  - JIT bugs are harder to debug than generated C you can read.
- **Size:** 8–10 lanes (§6).
- **Verdict:** recommended for `run` and `test` in the CLI.

### (d) LLVM

- **What:** like (c), through LLVM's C API (`inkwell`/`llvm-sys`).
- **Speed:** the best code. About the experiment's 13×, plus better
  inlining.
- **Tail calls:** `musttail` and `tailcc` (§2.10).
- **Tools:**
  - Links a large C++ library of one major version.
  - A heavy Nix build, and a new LLVM version to follow every six months.
    That is the cost Roc cites for leaving (§2.5).
- **Playground:** none.
- **Risk:** medium-high. **Size:** like (c), plus build plumbing.
- **Verdict:** not now. If (c) works, the gap between Cranelift and LLVM is
  the only thing LLVM adds, and the IR's simplifier already does the
  inlining that matters most.

### (e) Generate Rust

- **What:** IR to Rust source that uses `stitchwort-rt`'s types, compiled
  with rustc.
- **Speed:** like (b).
- **Tools:**
  - **Needs rustc and cargo on the user's machine.**
  - rustc is slow on large generated code: seconds to minutes per program
    **[inferred]**, Roc's complaint (§2.5).
  - Compile times would dwarf the run times this note is about.
- **Playground:** none.
- **Verdict:** no, except as a development aid: hand-written Rust, as in
  this note's experiment, is a good way to bound a gain.

### (f) Emit wasm, run it in a wasm engine

- **What:** IR to a wasm module, linked with the runtime compiled to wasm.
  - In the CLI it would run under an embedded engine (`wasmtime`).
  - In the browser it would run under the browser's own engine.
- **Speed:** native-ish code after the engine compiles it, minus wasm's
  overhead (§2.10). In the browser it would beat the machine-in-wasm by
  roughly what (c) beats the machine by natively **[inferred]**.
- **Stack safety:** the hard part.
  - Browsers give wasm a small stack (deep-recursion notes in
    stack-safe-evaluation.md).
  - Without stack switching (§2.10), deep non-tail recursion needs heap
    frames again. That gives back much of the gain.
- **Tail calls:** the tail-call proposal (§2.10).
- **Tools:** in the CLI, wasmtime is a large dependency: 19 MB in its
  default build (§2.10). That is more than Cranelift alone, which wasmtime
  itself uses to compile.
- **Playground:** **the only route that speeds it up a lot**. That is
  attractive for the static-site goal, but it's a second backend with its own
  runtime linking.
- **Risk:** high. **Size:** 10+ lanes.
- **Verdict:** not now. Revisit if the playground's speed becomes the
  bottleneck and stack switching ships widely. (c)'s translation from
  bytecode could be reused for it.

### (g) Through an existing backend: Chez Scheme

- **What:** IR to Scheme text, run by `scheme`. Idris 2's default; Unison's
  2022 plan (§2.3, §2.6).
- **Speed:** Chez is a good native compiler (§2.10). I have no measurement
  on our code: `scheme` isn't on this machine's path.
- **What you get:**
  - Big numbers, proper tail calls and deep recursion come for free.
  - Effects need closures only (§4.1). Ticks are data a Scheme runner would
    step: a second runner to keep identical, as `--js` has.
- **What you lose:**
  - Reference counting and reuse: Chez has a tracing collector. The
    in-place updates of fast-runtime.md's stage 4, and Perceus-style gains
    generally, don't carry over.
  - Every runtime service (big numbers, text natives, the effect loop, the
    `Delay` runner) is written again in Scheme.
- **Tools:** users need Chez installed (§2.10).
- **Playground:** none.
- **Risk:** medium. Idris shows it works, and Unison's apparent retreat shows
  the cost of a second runtime. **Size:** 6–8 lanes, like the JS backend.
- **Verdict:** no. It duplicates the runtime and gives up the memory model
  the machine was built around.

### 5.1 The routes side by side

| Route | Gain over the machine (`Set`) | Tools at run time | Playground | Keeps the Rust runtime | Size |
|---|---|---|---|---|---|
| (a) faster interpreter | 1.3–2× [inferred] | none | yes | yes | 2–3 lanes |
| (b) C | ≤13× [ran, upper bound] | a C compiler | no | via a C ABI | 8–12 |
| **(c) Cranelift** | ≤10×, est. 4–8× | **none** | no (keeps the machine) | **yes, directly** | **8–10** |
| (d) LLVM | ≤13× | none (but a heavy build) | no | yes | 10+ |
| (e) Rust | ≤13× | rustc, cargo | no | yes | 6–8 |
| (f) wasm | less than (c) natively | wasmtime (CLI) | **yes** | in wasm | 10+ |
| (g) Chez | unmeasured | `scheme` | no | no: rewritten | 6–8 |
| representation (unboxed fields) | another ~5× on top | — | helps the machine | yes | 4–6, after (c) |

## 6. Recommendation and staged plan

**Recommendation.**
- Route (c): a Cranelift backend in `crates/rt`, compiling the machine's
  bytecode to machine code in-process, for the CLI's `run` and `test`.
- The playground keeps the machine.
- A little of route (a) where it is cheap and helps the playground.
- The representation project after (c) works.

**Why bytecode, not IR, as the input** **[inferred]**:
- `code.rs` has already decided registers, moves, drops and reuse.
- Translating instruction by instruction means the native code makes
  exactly the machine's memory and counting decisions. That makes
  differences far easier to find.
- It also means stage N1 can be a narrow, checkable translation rather than
  a new compiler.
- Later, a direct IR-to-Cranelift path can come for better code, if
  profiles say so.

**What must stay identical** (the acceptance bar for every stage):
1. **Output and how a run ends**, against the reference evaluator and the
   machine:
   - the differential tests `crates/rt/tests/machine.rs`,
     `crates/cli/tests/run_reference.rs`, `run_js.rs`,
     `effect_differential.rs` (random effectful programs) and
     `crates/driver/tests/differential.rs`;
   - each run with a third runner added.
2. **Tick counts for partial code:** the same `Delay` values stepped by the
   same runner (§4.2); the tick-limit tests.
3. **Stack safety:**
   - a million-deep non-tail recursion runs;
   - a deeper one is `E-RESOURCE`, after the same output;
   - a 3,000,000-step tail loop runs in constant stack, including mutual
     tail calls;
   - a long effectful `List.map` runs.
4. **Resource limits:** with §4.3's counting, `E-RESOURCE` at the same
   points as the machine. That's a stronger check than stage 3 had.

**Stages** (one lane each unless noted):

| Stage | What | Done when |
|---|---|---|
| N0 | Spike: Cranelift as a dependency behind a Cargo feature (off in the wasm build). JIT one hand-built function on macOS arm64 and Linux x86-64. Measure the binary growth and compile time. **Check on macOS that JIT code runs in an unsigned development build, in a signed build, and in a hardened build** (and a notarised one, if we ship that), and what entitlement or `MAP_JIT` use each needs (§2.10). | It runs, in Nix, and `nix flake check` builds both with and without the feature; the three macOS cases are recorded |
| N1 | Translate the core instructions: `Move`/`Take`/`Drop`, `Const`, `Call`/`TailCall`/`Return`, `Switch`/`Field`/`Unpack`, `Ctor`/`CtorReuse`, `Test`/`JumpIfFalse`/`Jump`, and `Nat` fast paths with runtime calls for the slow paths. **Frame and step counters**, counted as the machine counts them, so the speed measured includes the bookkeeping native code will really have. Whole reachable islands (§4.6): an entry point whose reach has an unsupported instruction runs wholly on the machine. A debug-only allocation trace (below). Behind `run --native`. | `micro_call`, `micro_tail` and the `Set` benchmark run and agree, **with counters in**; **first real speed measurement**, stop point at 3× |
| N2 | Split in two (D1279). **N2a** (built, [below](#n2a-as-built-25-october-2026-d1279)): registers in machine registers, counters in registers. **N2b** (built, [below](#n2b-as-built-26-october-2026)): the big-stack thread and the full `E-RESOURCE` handling; tail calls between functions (`return_call`), with the tail-call tests below. | §6's stack-safety tests pass under `--native`, and the counter fires before the stack on every supported target |
| N3 | The remaining instructions: closures, `Apply`/`Pap` (eval/apply), `Int`/`Text`/`NumSwitch`, `Captured`, `Global` constants. Built, [below](#n3-as-built-26-october-2026-d1285). | Every function compiles; `machine.rs`'s differential tests pass under `--native` |
| N4 | Effects: the effect loop calls compiled continuations; `Text.fold`; the `Delay` runner. | `effect_differential.rs` and the partial tests agree three ways |
| N5 | Run the whole differential suite with `--native` added; fix what it finds. | All agree |
| N6 | Make `--native` the default for `run` and `test` in the CLI (the machine stays as `--machine`, the playground's runner and the fallback); a benchmark in `bench/`. | Decision at the time, like D386 |
| N7–N8 | Tuning from profiles: keep counters in registers, avoid materialising `Ordering`-like tags, inline more runtime fast paths. | Measured gains |
| R1–R4 (later) | Representation: unboxed `Nat`/`Int` fields and smaller nodes, by type, in the IR. Helps both runners. | Its own design note first |
| A1–A2 (any time) | Machine tuning for the playground: frame entry without register clearing, a few superinstructions. | Measured gains |

Stage N1 is the checkpoint. If the `Set` benchmark is not at least 3× faster
than the machine there, with the frame and step counters in, stop and
re-plan before N2.

**N2's tail-call tests.** "Cranelift has `return_call`" doesn't prove every
Stitchwort tail call lowers without a frame. N2 must show constant stack for
each of these shapes, with a loop of millions of steps:
- self tail calls (loops) and mutual tail calls between functions with the
  same signature;
- tail calls between functions with **different signatures** (argument
  counts and types, so registers against stack-passed arguments);
- a tail call **next to runtime calls** (a call to a primitive or to the
  freeing code just before it, and drops on the way out);
- a tail call that **crosses the native/machine boundary**: under whole
  islands there is no such call, so the test is that such a program runs
  wholly on the machine and agrees; if per-function mixing is ever added,
  this becomes a real test;
- **later closures** (N3): `TailApply` of a closure and of a partial
  application, including over-application.

**Bring-up trace (N1 to N4).** A debug-only trace of `alloc`, `reuse`,
`inc`, `dec` and `free`, with object identities normalised (numbered by
first appearance), emitted by both the machine and the native code and
compared between them. The aim is to check that native code makes the same
memory-management decisions as the bytecode, so the first differing event
points at the bug. It is bring-up instrumentation, compiled out of release
builds, not a permanent test invariant.

## N1 as built (25 October 2026)

**[ran]** Stage N1 is in `crates/native/src/n1.rs`, with the runtime side in
`crates/rt/src/native_abi.rs`, behind `stitchwort run --native` (CLI feature
`native`; `--verbose` says what ran natively and why not).

**What it compiles.** The N1 list plus `NatCase`/`NatPred`/`NumSwitch` (the
census's reading), `DropReuse`, `Global` and `Apply`/`TailApply`
(`census::n1_blocker` matches). Each bytecode body becomes one Cranelift
function in the `tail` calling convention taking and returning values as
three machine words each, in the machine's own `Value` layout (`#[repr(u8)]`,
checked at startup by `native_abi::probe_layout`). Inline: reference counts
(but through the runtime when tracing), the `Nat` `Add`/`Sub`/`Mul`/`Leq`/`==`
fast paths, `NatCase`/`NatPred`/`NumSwitch` on small numbers, `Switch`, and
the unique-cell paths of `Unpack`/`CtorReuse`. Everything else (big numbers,
other primitives, constructing cells, freeing) is an `extern "C"` call into
`native_abi`. Self tail calls jump; other tail calls are `return_call`.

**The crossing.** Admission (`plan`) takes the distinct `Call` targets of
`main`'s entry body as roots; each root's whole reachable island
(`census::island`) must fit, and every `Apply` in it must see only compiled
functions or applicable natives of the arity it applies. If any root fails,
the **whole run** stays on the machine, with a note. Otherwise the machine
runs the glue and, at a `Call` from the entry body to a root, hands the
arguments to native code (`State::native`, `NativeIslands::call`) if none of
them holds a function value made outside (which native code couldn't call);
the call then runs to its result natively. Steps and frames are counted
exactly as the machine counts them (D1253): native code carries the
machine's counters in a `Context`, checks them at each step and frame, and on
running out releases what its frames hold and returns an error code that the
machine turns into the same `E-RESOURCE`. Constants (`Global`) share the
machine's cache, so each is computed once whichever runner gets there first.
The run's thread gets a 4 GiB stack, and native code also checks the stack
pointer against a limit 16 MiB short of it at each frame, a margin until N2
sizes it.

**Agreement** (`crates/native/tests/n1.rs`, about 2 s): the three benchmarks
at small sizes and two small programs (big numbers past `u64::MAX`; mutual
tail recursion, constants and reuse) print what the machine prints; the
allocation traces of `set_nat` and the second program are identical event for
event (69,455 events for `set_nat`) and free every cell; the least frame
limit and the least step limit under which a 3,000-deep recursion finishes
are the same on both runners, one less is the same `E-RESOURCE` on both, and
running out mid-recursion frees everything. `stitchwort run --native
--alloc-trace` writes a byte-identical trace to the machine's for `set_nat`.

**The measurement** (`task native:bench`; best of 3 wall seconds; Apple
silicon, release build; machine heavily loaded, load average 29–38 during
the run, so absolute numbers are noisy):

| Program | Machine | `--js` | `--native` | Native vs machine |
|---|---|---|---|---|
| `set_nat` (1,000,000 keys) | 10.13 | 3.49 | 3.85 | 2.6× |
| keys only | 0.56 | 0.58 | 0.37 | 1.5× |
| **`Set` inserts** (the difference) | 9.57 | 2.91 | 3.48 | **2.7×** |
| `micro_call` (20,000,000 calls) | 1.06 | 0.50 | 0.27 | 3.9× |
| `micro_tail` (20,000,000 iterations) | 0.82 | 0.60 | 0.20 | 4.2× |

**Verdict: below the 3× stop point on `Set`** (2.7× on the inserts, 2.6× on
the whole run), and slower than Node on it. By the plan, N2 waits for
re-planning.

**Why, from a profile** (macOS `sample`, 2 s of the native `Set` run, one
sample, CPU contended so the shares are approximate): of the worker
thread's samples about 41% are in the compiled code; about 32% in the
allocator (`mi_free`, `mi_malloc`, page-queue searches, abandoned-page
reclaim) and `mach_absolute_time` (which mimalloc calls when it collects);
about 18% in freeing (`drop_glue` of `Value`, `value::free`, `Fields::drop`,
`Rc::drop_slow`); `sw_apply_target` about 5% (the `compare` function value
looked up at every `Apply`), `sw_ctor` 3%.

What that does and doesn't show:
- **Dispatch is gone as the main cost.** In the machine's profile the run
  loop was about two thirds of the samples; here the compiled code is under
  half.
- **The layout alone doesn't explain the rest.** §3.2's "uniform" Rust used
  this same layout (`Value`, `Rc<[Value]>`, mimalloc, reuse) and did the
  inserts in 0.7–0.9 s, against 3.5 s here.
- **The allocator costs more per cell than on the machine.** The traces
  prove both runners allocate and free exactly the same cells. Yet the
  machine's profile had about 7% of about 10 s in allocation (about 0.7 s),
  and this one about 32% of 3.5 s (about 1.1 s), mostly in mimalloc's slow
  paths: page-queue searches, abandoned-page reclaim and cross-thread
  collection. **[speculative]** Something about how native code frees (the
  order, or the thread its cells were made on) is pushing mimalloc off its
  fast path. Not investigated, by the stop rule.
- **[inferred]** Other candidates, none tried: make and free cells inline in
  compiled code rather than through `sw_ctor` and `Value`'s drop glue;
  resolve `Apply` of a known global at compile time; keep the counters in
  registers.

### The miss investigated (D1261, 25 October 2026)

**[ran]** A short investigation of why `Set` missed 3×. The machine was
shared throughout (load averages 5–80), so the evidence below leans on
counts that don't depend on load: instructions retired and cycles from
`/usr/bin/time -l`, mimalloc's own statistics (`MIMALLOC_SHOW_STATS=1`),
and the allocation trace.

**1. The allocator does the same work on both runners; the thread
hypothesis is refuted.**
- Both runners run everything (compiling, constants, cells, freeing) on
  the one worker thread `driver::with_stack` starts; only its stack size
  differs. Running the machine on the 4 GiB stack changed nothing
  (177.7 G instructions, 40.0 G cycles either way).
- mimalloc's statistics are identical for the two runners: 8.2 M pages
  "abandoned" and 8.2 M "reclaimed on free" in one run. That isn't
  cross-thread traffic. It is mimalloc 3.3.2 on a single thread: when a
  small page fills up beyond `page_full_retain` (2), it is abandoned, and
  the next free into it reclaims it.
- `mach_absolute_time` comes from the same path: each abandonment calls
  `_mi_arenas_collect` (`_mi_page_abandon` → `mi_arenas_try_purge` →
  `clock_gettime`), so it's 8.2 M clock reads per run, on both runners.
- `MIMALLOC_PAGE_FULL_RETAIN=-1` (never abandon) removes the same 5.6 G
  instructions from both runners and about 7% of the cycles (machine −1.4 G,
  native −1.0 G).
- The hand-written Rust (below), doing the IR's allocations, also shows
  8.2 M abandonments.
- What remains is that sampling puts about 1.0 s of the native run in the
  allocator, against about 0.7 s for the same calls in the hand-written
  Rust. **[speculative]** Native code's frames touch more memory (every
  register is a 24-byte slot in memory), so the allocator's data is colder.
  Not measured further.

**2. §3.2's "uniform" Rust didn't do the same work as the IR.** The
allocation trace for 20,000 keys has, per insert, about 14 cells made,
14 freed, 28 increments and 43 decrements, and only 0.5 reuses (`reuse` is
29,372 events, 20,000 of them in the keys). The cause is in the IR, so
it's the same on both runners:
- `insertWith` takes a node apart with `Unpack` without a reuse token,
  since the rebuilt node is made in another function (`rebuild`'s `Keep`
  arm is `Map.Tree.bin`, a fresh `Ctor`). So each level frees its node on
  the way down and allocates a new one on the way up.
- `shape` is passed clones of both subtrees: two increments and two
  decrements per level.

The hand translation reused the node's cell at every level and borrowed
for `shape`. A variant that does what the IR does (`ir` in Appendix A:
free on the way down, a fresh node in `rebuild`, clones for `shape`) takes
**1.8–2.0 s**, against 0.68–0.73 s for "uniform", in the same conditions.
So of §3.2's 10–13×, about 2.6× was reuse that today's IR doesn't do.

**3. Where the native time goes now.** Sampled, with native addresses
mapped to bodies: about 57% in compiled code (`shape` 38% of that,
`insertWith` 24%, `Nat.compare` 23%, `rebuild` 15%), about 34% in mimalloc,
and about 9% in runtime glue. Native code retires about 49.5 G instructions
for the inserts, the `ir` Rust about 24.9 G (the whole run). The extra is
the code shape:
- registers are a stack slot of three-word values, so each instruction
  loads and stores words;
- every frame erases its registers on entry and releases them on return;
- each call counts steps and frames through the context.

For example, `Nat.compare` is 70-odd instructions for two loads and two
comparisons.

**What changed** (agreement unchanged: the `n1.rs` tests pass, traces
identical; a new check runs the trace with inline counting, as `run
--native` does, and asserts the same cells are made and every one freed):
- **`Apply` caches its target.** Each `Apply` site has an `ApplyCache` (the
  last function value applied there, kept alive so that its address can't
  be reused, and its code). A function value at the same address calls the
  cached code with no runtime call. In `insertWith` the dictionary is a
  parameter, so it isn't known at compile time; the cache does the job.
  (`sw_apply_cached`, replacing `sw_apply_target` in compiled code.)
- **An emptied cell is freed directly.** After a unique `Unpack` without a
  token that took every field, the cell is deallocated (`sw_free_emptied`)
  without `Value`'s drop glue walking five `Erased` fields.
- **`sw_ctor`** copies the fields into an uninitialised slice instead of
  collecting an iterator.

Together: −6% instructions and −5% cycles on the native inserts.

**The measurement**, best of 3, interleaved old and new binaries, load
average 24–36:

| Inserts (1,000,000 keys) | Wall s | Cycles (G) | Instructions (G) | vs machine (cycles) |
|---|---:|---:|---:|---:|
| machine | 9.86 | 38.9 | 171.6 | 1× |
| `--native`, N1 as merged | 3.44 | 13.5 | 52.7 | 2.88× |
| `--native`, now | 3.28 | 12.9 | 49.5 | **3.02×** |
| hand Rust, `ir` (same work as the IR) | 1.94 | — | — | ~5× |
| hand Rust, "uniform" (§3.2, with reuse) | 0.73 | — | — | ~13× |

`task native:bench` (best of 3; load 15 falling to 7): machine 9.87 s,
`--js` 3.41 s, `--native` 3.33 s on the inserts, **3.0×**. Earlier the
same day, under a load average of 81, it gave 2.9×. `micro_call` 3.9×,
`micro_tail` 3.3×.

**Verdict: on the line, not clearly over it.** `Set` is at 3.0× in cycles
and in a quiet-ish wall-clock run, and 2.9× under load. That's not a clear
pass of the 3× stop point, so N2 stays waiting for the re-plan.

**What it would take**, ranked by expected gain against size:
1. **Registers as SSA values, not a memory slot** (Cranelift variables for
   the words of non-escaping registers; no erase of registers already
   empty; no reload after a store). This is the 2× instruction gap to the
   `ir` Rust, so it could reach about 4–5×. Size: large, the core of an
   N2-style code generator.
2. **Reuse across the `insertWith` → `rebuild` call, and borrowing for
   `shape`** (an IR change: inline `rebuild`/`balance` so `CtorReuse`
   applies, or pass the token; let `shape` read sizes without clones).
   Worth about 2.6× on the hand code, and it speeds the machine too, so its
   effect on the ratio is uncertain; it's the bigger absolute win. Size:
   medium to large, in the machine's compiler, not the native backend.
3. **Allocation and freeing inline** (call the allocator with a known
   layout and write the header in compiled code; free emptied cells
   inline). The runtime glue is about 9% now; perhaps 5–10%. Size: medium.
4. **mimalloc's `page_full_retain = -1`** for the CLI: about −7% of cycles
   on both runners, which nudges the ratio to about 3.1×. Size: small, but
   it's process-wide, so `check` workloads would need measuring first.
5. **Counters in registers.** A few loads and stores per call, so a small share.
   Size: medium.

## N2a as built (25 October 2026, D1279)

**[ran]** Item 1 of the ranked list above: registers in machine registers.
In `crates/native/src/n1.rs` (its module comment has the details).

**Registers.** Each bytecode register is three Cranelift variables, one
per word of its value, so Cranelift allocates machine registers and spills
only what it must. An empty register's words are all 0 (`Erased`): a move
out sets them so, which costs nothing, so registers known to be empty are
never erased in memory and never dropped (`full`, the forward analysis N1
already had, says which registers a write, a return or an exit must drop).

**The boundary with the runtime.** Values go to memory only where a Rust
helper takes a pointer, and then as the machine would have them in its
register vector:
- a helper that reads values (a native operation's slow path, a test, a big
  number's `NumSwitch`) borrows copies of the words in a spill slot;
- a helper that takes a value (`DropReuse`'s source, `CtorReuse`'s token)
  is given it in a spill slot, and the register is empty after;
- a helper that writes a register (`Prim`, a big `NatPred`, `DropReuse`'s
  token) writes an empty spill slot, and the value is then assigned to the
  register like any other write, the old value dropped after, in the
  machine's order;
- under the trace, `Unpack` goes through the runtime on every register,
  written out and read back.

Each value is in exactly one place at a time, and every move, clone and
drop is the bytecode's. `sw_inc` now takes the three words, not a pointer.

**Error exits.** N1 had one unwind block that released the register slot.
With registers in variables, each point that can stop (a step, a frame, an
error after a call) has its own cold exit, which writes the registers that
may hold a value there into the spill slot and releases them, highest
first, as before.

**Smaller wins that fell out:**
- **Counters in registers.** The steps left are in Cranelift's pinned
  register (x21 on arm64, r15 on x86-64): the trampoline loads it from the
  context, keeps the host's value of the register, and writes the steps
  back after. The frames pending are an argument of every body, so a
  return needs no decrement. Counting stays exact (the `n1.rs` resource
  tests).
- **No field erases for a freed cell.** After a unique `Unpack` without a
  token that takes every field, the cell is freed as `MaybeUninit` values
  (`sw_free_emptied`), so the fields needn't be erased first (N1 erased
  them, and its "free without a walk" still walked them). About −2 G
  instructions on `Set`.
- The spill slot is sized to the most registers an exit releases, not to
  every register.

Not done: an inline `Nat.compare` fast path. `compare` is called through
`Apply` on a dictionary, so it can't be inlined without knowing the target;
its body's fast path is already inline. What it costs now is mostly its
prologue (callee-saved registers that only its slow paths need).

**Agreement.** The `n1.rs` tests pass unchanged (outputs, event-identical
allocation traces, the least step and frame limits). A new test,
`every_error_exit_frees_the_live_registers`, runs a program with values
live across direct calls, `Apply`, a constant's first computation and tail
calls under every step limit and every frame limit up to the least that
finishes, and checks each stops as the machine does and frees every cell.
Breaking the exits' release on purpose fails it; the older tests didn't
notice.

**The measurement** (Apple M4 Pro, release; load average 25–57, so wall
times are rough; cycles and instructions from `/usr/bin/time -l`, best of 3
by cycles; inserts are `set_nat` minus the keys, as before):

| Program | Runner | Wall s | Cycles (G) | Instructions (G) | vs machine (cycles) |
|---|---|---:|---:|---:|---:|
| `Set` inserts | machine | 9.64 | 38.1 | 171.6 | 1× |
| | `--native`, N1 | 3.24 | 12.6 | 49.5 | 3.0× |
| | `--native`, N2a | 2.75 | 10.6 | 41.0 | **3.6×** |
| | hand Rust, `ir` (whole run) | 1.89 | 7.4 | 24.8 | 5.1× |
| `micro_call` | machine | 0.92 | 3.58 | 18.9 | 1× |
| | `--native`, N1 | 0.22 | 0.81 | 3.95 | 4.4× |
| | `--native`, N2a | 0.17 | 0.61 | 2.88 | **5.8×** |
| `micro_tail` | machine | 0.59 | 2.29 | 14.8 | 1× |
| | `--native`, N1 | 0.16 | 0.58 | 2.83 | 4.0× |
| | `--native`, N2a | 0.12 | 0.43 | 2.08 | **5.4×** |

`task native:bench` (best of 3 wall seconds, load average 47–57 falling to
28): inserts machine 10.30, `--js` 3.41, `--native` 2.61 (**3.9×**);
`micro_call` 5.3×, `micro_tail` 4.4×. Native is now faster than `--js` on
every program.

**Where the rest goes** (macOS `sample`, 2 s of the `Set` run, samples
mapped to bodies with `STITCHWORT_NATIVE_DUMP`'s addresses): about 43% in
compiled code, about 41% in mimalloc, about 10% in freeing (`Value`'s drop
glue, `sw_free_emptied`) and the rest in glue (`sw_ctor`'s copy). Of the
compiled code's samples, `insertWith` has 60%, mostly on the loads of a
node's counts and fields (cache misses on the tree, which the hand Rust has
too). The instruction gap to the `ir` Rust is now 1.65× (was 2×). What's
left of it in the code generator: wide bodies take most arguments on the
stack (three words a value), and Cranelift copies them into its own spill
slots on entry; values live across calls spill too. Packing a value into
fewer words, or inline allocation and freeing (item 3), are what's next on
that front; item 2 (reuse across `rebuild`) and item 4 (mimalloc's
`page_full_retain`) are unchanged by this stage.

## N3 as built (26 October 2026, D1285)

**[ran]** Closures, partial application, unknown calls, and the `Int` and
`Text` instructions, in `crates/native/src/n1.rs` and
`crates/rt/src/native_abi.rs` (their module comments have the details).
Effects stay for N4.

**Function values are the machine's.** A `Fun` is now `repr(u8)`, like
`Value`: its variant byte, then a global's or lambda's index at byte 4, then
a closure's captures (`Box<[Value]>`, address and length) at bytes 8–23.
`probe_layout` checks it at run time with the rest. Native code reads the
captures itself (`Captured` is a load and a clone), and makes closures and
partial applications through the runtime (`sw_closure`, `sw_pap`), so the
machine and native code pass function values to each other as they are.

**Two calling conventions.** A global's body keeps N1's: the context, the
frames pending, three words per argument, three words back, in Cranelift's
`tail` convention. A lambda's body takes one more word last: the function
value's `Rc` word, which it owns and drops when it returns, tail-calls or
leaves by an error exit. Each global function that can be a value gets a
tiny adapter with the lambda's signature (drop the value, `return_call` the
body), so every function value, global or closure, is called the same way;
direct calls never go through the adapter.

**Apply: a fast path and one slow path, as the machine's eval/apply.** An
`Apply` whose target is a closure or global taking exactly as many
arguments as it passes, with nothing yet applied, is an indirect call. Each
`Apply` keeps the last target it saw (`ApplyCache`), keyed by the first word
of the `Fun` masked to its variant and index, so a hit is a compare and a
call, and a miss one runtime lookup (`sw_apply_cached`). Everything else (a
partial application to extend, too few arguments making a new partial
application, too many applying the result to the rest, a native operation
as a value, `DoneK`) goes to one shared stub per argument count
(`apply{n}`). Its runtime half, `sw_apply_prepare`, does what the machine's
`apply` and `enter` do, with the clones and drops in the same order; the
stub then counts the step, checks the frame, and calls the code it was given
(switching on its arity), looping on the arguments left over. A `TailApply`
is a `return_call` to the target or to the stub, so tail applies don't grow
the stack.

**Islands.** The plan's old rule (every function value an island can make
must be a compiled global taking as many arguments as each `Apply` passes)
is gone: any function value works. The function values the entry body makes
are compiled too when their islands fit ("guests"), so a root given the
entry's lambdas runs natively. At the crossing, a root whose island applies
function values is handed the call only if every function value in its
arguments, inside data, captures and partial applications, has compiled
code (`natively_callable`); otherwise that call runs on the machine and a
note says why.

**The cheap find** (the standalone note's S6). The `Int` instructions
(`IntCase`, `IntOfNat`, `IntNegSucc`), `Text.chars`, `Unreachable`, and every
`Prim`/`Test` the runtime already implements without frames, through the
existing `sw_prim`, were a few dozen lines, so they came in with N3; `Int`
comparisons and small `IntCase` are inline. Left out: the effect operations
and `Text.fold` (which runs a function over the machine's frames).

**Agreement** (`crates/native/tests/n3.rs`; the helpers both test files use
are in `tests/common/`). Programs with `map` and `fold` over lambdas,
closures capturing several values (one a list), partial applications of
globals and closures, unknown functions under-, over- and exactly applied,
function values in lists, continuation chains of closures, partial
applications and over-applications, and the `Int` and `Text` operations
with big integers: same output, the same allocation trace event for event,
every cell freed. Function values cross both ways (the entry's closures and
partial applications applied by a native root; a closure a native root
returns applied by the machine). Tail applies of all three kinds run
1,000,000 deep under a frame limit of 100 on a 64 MiB stack; turning the
exact tail apply into a call overflows the stack, so the test does see it.
Under every step limit and every frame limit up to the least that finishes,
a program with closures live across calls, applies and tail applies stops
where the machine does and frees every cell; dropping the closure's release
from the error exits fails it (leaked at limit 22). Two `n1.rs` tests that
expected function values and `Text` to stay on the machine now use
`Text.fold` for that. One fix to the trace test along the way: the runtime
keeps a per-thread cache of the ASCII `Char` cells (`prims::char_value`), so
the first run on a thread allocated 128 cells the second didn't; the test
now warms it first.

Not done: running `machine.rs`'s differential tests under `--native` (the
table's "done when"). There's no harness for it yet; the N5 run of the whole
suite is where it belongs.

**Census** (`dev opcode-census`, bodies whose own island fits, of those
reachable; the standard library's in brackets):

| Program | Before N3 | After N3 | What still blocks |
|---|---:|---:|---|
| `Rogue.main` | 86/244 (32/54) | 170/244 (43/54) | effects only: `Bind` 113, `Translate` 6, `FoldIn` 2, `RunPure` 1 |
| AoC day 1 | 24/56 (14/26) | 45/56 (23/26) | effects only |
| AoC day 2 | 20/59 (13/22) | 41/59 (17/22) | effects only |
| AoC day 3 | 23/56 (15/25) | 43/56 (22/25) | effects only |
| AoC day 4 | 21/52 (16/26) | 49/52 (26/26) | effects only |
| AoC day 5 | 29/67 (21/32) | 47/67 (25/32) | effects only |
| AoC day 6 | 42/68 (30/38) | 65/68 (38/38) | effects only |
| AoC day 7 | 30/68 (20/36) | 60/68 (36/36) | effects only |
| AoC day 8 | 60/97 (49/60) | 84/97 (56/60) | effects only |
| AoC day 9 | 68/105 (53/65) | 92/105 (61/65) | effects only |
| `set_nat`, `micro_call`, `micro_tail` | 15/16, 2/3, 1/2 | all | — |

Every remaining blocker in these programs is an effect operation (`Prim` or
`TailPrim` of `Effect`); `Text.fold` doesn't occur in them. But none of the
real programs runs natively yet: the rogue's entry calls only lambdas, and
the AoC entries call nothing directly (`main` is effectful glue), and the
plan only takes `Call` targets of the entry as roots. Rogue's one big root
(`lambda #159`, 242 bodies) is blocked by effects alone.

**The measurement** (Apple M4 Pro, release; load average 42–71, so wall
times are rough; cycles and instructions from `/usr/bin/time -l`, best of 3
by cycles). `bench/native/closures.sw` at 1,000,000 elements: `List.range`,
`List.map` with a lambda capturing two values, `List.filter` with a lambda,
`List.foldLeft` with a lambda, `List.map` with a partial application, and
`List.foldLeft` with a global function. "Work" is the run minus the same
program at size 1 (parsing, checking and lowering the standard library: 0.54
G cycles; native adds 0.13 G instructions for compiling, 10 ms).

| Program | Runner | Wall s | Cycles (G) | Instructions (G) | vs machine (cycles) |
|---|---|---:|---:|---:|---:|
| `closures`, work | machine | 0.50 | 2.01 | 11.39 | 1× |
| | `--native` | 0.26 | 1.00 | 3.47 | **2.0×** (3.3× instructions) |
| `closures`, whole run | machine | 0.68 | 2.55 | 12.97 | 1× |
| | `--native` | 0.44 | 1.57 | 5.18 | 1.6× |
| `Set` inserts | machine | — | 39.9 | 171.7 | 1× |
| | `--native`, N2a | — | 10.6 | 41.0 | 3.6× |
| | `--native`, N3 | — | 11.0 | 42.1 | **3.6×** |
| `micro_call` | `--native`, N3 | 0.17 | 0.62 | 2.88 | 5.8× (N2a 0.61, 2.88) |
| `micro_tail` | `--native`, N3 | 0.13 | 0.43 | 2.08 | 5.7× (N2a 0.43, 2.08) |

The micro benchmarks are unchanged to the instruction. `Set` inserts are
about 1.1 G instructions (3%) above N2a; not investigated (the inserts apply
`compare` through a dictionary, and that `Apply` now goes through the new
cache check, which is a guess, not a measurement).

**Where the closure benchmark's time goes** (macOS `sample`, 1 s of six
runs back to back, samples mapped with `STITCHWORT_NATIVE_DUMP`'s
addresses). About 22% of the samples are on one instruction: the return
point of `List.map`'s non-tail recursive call (offset 0x394 of its code,
the `sub sp` just after the `bl`). **[inferred]** That is the cost of a
recursion a million frames deep coming back: the stack it returns into is
cold, and the return predictor can't hold a million returns; the samples
land on the first instruction after the return. About 9% is `Nat` `%`,
which goes through `sw_prim`, `prims::eval` and `prims::div_fuel` every
time (N1 has no inline `%`); about 14% is `mi_malloc`/`mi_free`/`Value`
drop glue. The partial application `add offset`, applied once per element
on the slow path, is about 8%: `sw_apply_prepare` (2.5%), a cache lookup
that can't hit (1%), and **[inferred]** the `Vec` growth and `realloc` of
merging its arguments (5%).

**What N4 needs, for the rogue standalone:**
1. **Effects.** `Prim:Effect` and `TailPrim:Effect` (`Bind` nearly
   everywhere; `Translate`, `FoldIn`, `RunPure` in the rogue), which means
   native code building and returning the machine's effect values and the
   effect loop calling compiled continuations (which are now ordinary
   compiled closures).
2. **Roots beyond the entry's `Call`s.** The entry's lambdas (the rogue)
   and effectful glue (AoC) are where the work starts, so the plan has to
   take the function values the effect loop runs as roots too, not only the
   entry's direct calls.
3. `Text.fold` and the `Delay` runner (in none of the programs above, but
   in the stage's scope).
4. Cheap wins seen on the way, for N7–N8: an inline `Nat` `%` and `/`, and
   applying a partial application to exactly the rest of its arguments
   without building a merged `Vec` (a fast path beside the closure one).

## N2b as built (26 October 2026)

**[ran]** The safety work left after N2a. In `crates/native/src/frames.rs`,
`n1.rs` and `crates/native/tests/{n2b,frames}.rs`.

**Stack sizing.** The stack-pointer check behind the frame limit used a
fixed 16 MiB margin. Now:
- **Each body's frame size** is read from what Cranelift emitted (0.136
  doesn't report it). On aarch64 the machine buffer's unwind
  pseudo-instructions (`PushFrameRegs`, `DefineNewFrame`, `StackAlloc`) sum
  to the frame (a body measured by hand: 304 bytes, the sum 304). On x86-64
  there is no `StackAlloc`, but the prologue is always `push %rbp; mov
  %rsp,%rbp; sub $N,%rsp`, so `N` is read from the code bytes. A frame of a
  page or more (probed first), or a prologue of another shape, takes a
  safe IR bound (stack slots and two spill slots a value; far above the real
  size). Every bound adds the widest signature's arguments as if all were
  on the stack (a tail call to a wider callee grows the frame by that), and
  16 for alignment. The measured bounds against the real use of a
  non-tail recursion (the least frame size that finishes, found by
  bisection while building this): 408 against 304 bytes a frame for one
  argument, 1392 against 1169 for six, 2720 against 2352 for twelve.
- **The rule.** A run is on the machine unless `frame limit × widest bound`
  fits the stack less `HOST_ROOM` (8 MiB, what the host used above the
  crossing) and `HELPER_ROOM` (8 MiB, what a runtime helper uses at the
  bottom) and one more frame (the check runs before a call pushes its
  frame). Then the frame counter always fires before the stack-pointer
  check, so the check is a backstop that never decides a run. The rule is
  `Islands::accepts`, which now gets the frame limit; a call it refuses runs
  on the machine and says so in the notes ("`f` ran on the machine: N frames
  of up to B bytes may not fit the S-byte stack"). `NATIVE_STACK` is now
  16 GiB (address space, not memory): the default limit of 2,000,000 frames
  fits levels of up to about 8,000 bytes. With N3 a level is a body (or an
  adapter, which tail-calls it) plus an apply stub that stays on the stack
  while it calls (the `Set` benchmark: about 1,260 + 1,100 bytes, which did
  not fit the 4 GiB it had); wider ones run on the machine at the default
  limit, or natively under a smaller `frames`.
- **Test** (`n2b.rs`, `recursion_to_the_frame_limit_stops_at_the_counter`):
  a non-tail recursion with 1, 6 and 12 arguments live across the call,
  limited to exactly the frames it needs, on exactly the stack the rule
  asks for, has the machine's output; one frame fewer is the machine's
  `E-RESOURCE`. A second test checks that a stack too small keeps the run on
  the machine. (A call with 17 arguments didn't reach native code
  in this test: its island is not admitted, for a reason not looked into.)

**Tail calls** (`n2b.rs`): `direct`, `through a function value` (a
`TailApply` of a global in each iteration, picked by the iteration's parity),
`mutual recursion`, `next to runtime helpers` (big-number arithmetic and
cell allocation each iteration), `wide argument lists` (13 arguments), `to a
wider callee than the caller's` (16 arguments, from a 2-argument caller),
and `from a frame with live registers to free`. Each runs 10,000,000
iterations on a 64 MiB thread (a leak of 8 bytes an iteration would end
it), and agrees with the machine at 200,000 on output; at 300 iterations
the traces are event-identical and the least step and frame limits equal.
Not covered: a loop that tail-calls itself through a function value (a total
function cannot, and `{Partial}` functions are not yet in the native
subset).

**Error exits and the trace.** The comparison found a real difference: N2a
released a leaving frame's registers highest first, as the machine releases
a *returning* frame, but a failed machine run drops everything with
`regs.clear()` (outermost frame first, each lowest register first, then a
tail call's fetched arguments). On an error, frames now hand their values
to the runtime (`sw_unwind`), which keeps them in segments, and the
machine, once it has cleared its own registers, has `release_unwound` drop
the segments last first. A tail call that runs out of steps fetches its
arguments first in the machine (moved or cloned), so the exit does too.
With closures (N3), a lambda's frame also holds its closure, and an
over-application's rest sits in the callee frame's `Ret`: the machine clears
its *frames* before its registers, so each leaving native frame pushes a group
(its closure, or nothing) that the machine has dropped, last frame first,
right after `frames.clear()` (`release_unwound_frames`), and the apply stub's
rest joins the callee's group. The stub's own early exit (out of steps or
frames before the call) drops as `push` returning its error does: the rest,
the closure, then the arguments, each lowest first (`sw_release_up`).
`closure_error_exits_make_the_machines_allocation_trace` sweeps a program of
closures applied exactly, partially, over-applied and tail-applied.
`error_exits_make_the_machines_allocation_trace` sweeps the traces at every
step and every frame limit up to the least that finishes, for N2a's program
and for the tail-call shapes that hold values; it failed before this.

**x86-64.** Rosetta runs here (`/usr/bin/arch -x86_64`), but the toolchain
has no x86-64 Darwin standard library, so the native tests were not run on
x86-64. What was checked: `tests/frames.rs` compiles bodies for both
architectures (Cranelift's x86 and arm64 backends are in the test build) and
checks that the prologue is read on each and the bound covers the stack
slots.

## N4 as built (26 October 2026, D1285)

**[ran]** Effects and handlers, in `crates/native/src/n1.rs`,
`crates/rt/src/native_abi.rs` and `crates/rt/src/machine.rs` (their module
comments have the details). `games/rogue` runs natively under `run
--native` with every body but the entry compiled, which is what milestone
M2 (`build --native games/rogue`, standalone S7) builds on.

**Nested machine and tail requests.** Native code doesn't reimplement the
effect runtime; the two runners call each other.

- *Machine to native.* The plan's roots and islands are gone. Every body
  `main`'s entry reaches (`census::island`) is compiled, except the entry
  itself (glue the machine runs once). The machine hands a call over
  wherever it would push a frame for a compiled body, whoever calls it: a
  `Call` or exact `Apply` in any machine frame, a `TailCall` or exact
  `TailApply` (after the same step and release as `replace`), and `enter`,
  which is how the effect loop applies a continuation and the `IO` runner
  steps a `Delay`. So the entry's lambdas (the rogue) and effectful glue
  (AoC) need no special case. `enter` doesn't call native code itself: it
  leaves the call to the run loop (`State::deferred`), so the function value
  and whatever else its Rust callers hold are dropped first, as they are
  when it pushes a frame. Without that, the allocation traces differed
  (`dec`s of a partial application's arguments came after the body instead
  of before).
- *Native to machine.* What native code doesn't compile, the machine runs
  for it, nested on top of what is pending (`machine::nested`; the
  machine's frames are on the heap, so this nests in Rust by one call): the
  effect natives other than `bind`'s common case (`foldComp` and its
  variants, `translate`, `runPure`: the machine's own code, so every effect
  value, count and allocation is the machine's), `Text.fold`, and a
  function value with no native code (resumptions, `StateRun`/`StateK`,
  `JumpK`, `DelayK`). `bind c k` is inline: `sw_bind` takes `c` apart, and
  for `Done x` native code applies `k` to `x` exactly as `Apply` does, so a
  compiled continuation is a direct call; otherwise the result is the node
  `Bind c k`.
- *Tail requests.* In a tail position, running the machine nested would
  grow the native stack by a frame per handled operation, so a loop through
  a handler would overflow. Instead native code returns a request
  (`TailRequest`: an apply or an effect native, with the frame's closure,
  which is dropped once the request has begun, as the machine drops a
  popped frame's). Frames return as on an error exit until a caller that
  isn't in a tail position performs it (`sw_perform`, at its own frame
  count), or the crossing returns it and the machine performs it with the
  frame's return. Effect loops run in constant native stack.
- *Counting.* The machine's frame limit counts native frames below a
  nested run (`frame_base`), and native code writes its step count to the
  context before every helper that runs the machine and reads it back
  after, so both runners count every step and frame by the machine's rules.
- *Error exits across the nesting* (with N2b's order). After a failed run
  the machine drops every frame's closure and pending return, outermost
  first, then every register, outermost first. With nesting, the stack
  alternates machine segments and native ones, so nothing is dropped where
  it fails: each crossing's frames hand theirs to the runtime
  (`sw_unwind`, as N2b built it), a failed nested run keeps its own frames
  and registers rather than truncating them, and both go into one log on
  the machine (`State::unwound`), innermost first. `release_failed` then
  drops the machine's own frames, the logged frames last-in first, the
  machine's registers, the logged registers likewise, and the tail
  arguments. N2b's every-limit trace sweeps and N4's handler sweep agree
  event for event.
- *The stack bound* (N2b's rule that the frame counter must fire before
  the stack check). Nesting puts runtime and machine frames between native
  ones, which N2b's bound didn't allow for. Measured (`frames::NEST_ROOM`):
  a recursion through `Text.fold` uses 2,104 bytes per counted frame, and a
  handler resuming in a non-tail position 3,904 (two nestings per frame),
  native frames included; handlers in other positions don't nest at all.
  So a program that can nest (it reaches an effect native, `Text.fold`, or
  a function value of one) allows 4 KiB more per frame (more than either measurement, native frames
  included; 6 KiB would keep the rogue's 2,000,000 frames off the 16 GiB
  stack, raising the stack to 32 GiB is the alternative); one that can't
  keeps N2b's bound. The check is now made once, when the machine is given
  native code (`NativeIslands::fits`), since every call can cross.
- *No host addresses* (S4). The new helpers are linked by name like the
  others, and the effect natives are passed as their place in
  `EffectOp::ALL`.

`run --native --verbose` reports, for the rogue, "running 241 of the 242
bodies `main` reaches natively (compiled in 693 ms)", and for each AoC day
all but the entry. Every AoC day on Matt's inputs prints the same answers
natively as on the machine; wall times (load ~45, one run each) are about
the same for the short days (0.25–0.35 s, mostly checking), day 4 0.99 →
0.47 s, day 8 3.48 → 1.20 s, day 9 2.38 → 0.98 s.

**Agreement** (`crates/native/tests/n4.rs`). A state-passing handler, `Fail`
caught as a value, a handler resuming more than once (`Pick.all`, each
resumption applied in a loop), a generator under a seeded state handler,
the rogue's `seeded` around partial code (a `foldD`), and `IO` printed in a
loop through the runner: the same output and the same allocation trace,
event for event. Every `-- run:` line of `effect-runtime.sw`,
`effect-handlers.sw` and `effect-state.sw` (resumptions stored, resumed many
times, through nested handlers and translations; state-passing handlers
every way they resume) lowered as an entry: the same value, the same
effect counts, the same trace, every cell freed. Under every step limit
and every frame limit up to the least that finishes, a program with a state
handler, a caught failure, a resumption used twice and `seeded` around
partial code stops where the machine does and frees everything. Effect
loops 250,000 long (a state handler's jumps, a fold resuming in a tail
position at the closed and the open row) under a frame limit of 100 on a
16 MiB stack. The open-row loop does reach a tail request (a lazy
resumption applied in a tail position; checked with a probe), but these
loops also pass with tail requests turned off, since a lazy resumption
returns to the handler's loop rather than nesting: no test yet shows a
shape where nesting would pile up and the machine's own frames don't (a
recursion whose tail position is a handler runs out of frames on the
machine too). Two `n1.rs` tests that expected `Text.fold` to keep code on
the machine now check that it runs natively.

**Census** (`dev opcode-census`; `n1_blocker` now accepts every
instruction, so "fits" is "compiled"):

| Program | After N3 | After N4 |
|---|---:|---:|
| `Rogue.main` | 170/244 (43/54) | 244/244 (54/54) |
| AoC days 1–9 | 45/56 … 92/105 | all (56, 59, 56, 52, 67, 68, 68, 97, 105) |

**The rogue** (seeded with 12345 in place of `IO.randomSeed`, as
`crates/cli/tests/build.rs` does): two key scripts piped to `run` and to
`run --native`, 29 keys (38,451 bytes of output) and 188 keys with stairs
(252,473 bytes): identical output, both exit 0.

**The measurement** (Apple M4 Pro, release, load average 40–52 so wall
times are rough; cycles and instructions from `/usr/bin/time -l`, best of
3; whole runs, which include about 1.07 G instructions of checking and
lowering, and 0.29 G more for compiling with `--native`).

| Program | Runner | Cycles (G) | Instructions (G) | vs machine (cycles) |
|---|---|---:|---:|---:|
| `closures`, whole run | machine | 2.59 | 13.14 | 1× |
| | `--native`, N4 | 1.51 | 5.15 | 1.7× (N3: 1.57, 5.18) |
| `Set` inserts | machine | 38.1 | 174.1 | 1× |
| | `--native`, N4 | 10.3 | 41.6 | **3.7×** (N3: 11.0, 42.1) |
| `effects`, whole run | machine | 9.93 | 50.17 | 1× |
| | `--native`, N4 | 7.90 | 40.21 | 1.26× |

`bench/native/effects.sw` at 1,000,000 of each: a state-passing handler
counting (`bump`, resumed with the state plus one) and a reader (`ask`).
Closures and `Set` are where N3 left them. The effects benchmark gains
little because its time is the effect runtime's, which native code calls:
each operation costs about 29,000 instructions on the machine for `bump`
and 20,000 for `ask` (linear: measured at 100,000 and 300,000), and native
code takes off only the handler's and the loop's own bodies (22,000 and
16,500). **[inferred, not profiled]** That cost is in building and taking
apart the effect runtime's values and handler records for each operation,
which N4 deliberately leaves to the machine; it is the place to look before
making handlers native.

**What S5–S7 need from N4.** Native code now calls back into the machine
(`machine::nested`, `machine::perform`) for effects, `Text.fold` and
uncompiled function values, so a standalone executable links the machine
as a runtime library, not just the value layout and the helpers (as D1287
already has it). S7's "both entry callees are native islands" becomes
"every body but the entry is compiled": there are no islands any more. And
`sw_bind`, `sw_effect`, `sw_fold`, `sw_tail_effect` and `sw_perform` are new
helper symbols for the relocatable code to reach through the tables. The
crossing is now per call, not per island root (`NativeIslands::call(code,
env, args, run)`), with one trampoline per arity. Compiling the whole
reachable program takes 0.7 s for the rogue, which ahead-of-time
compilation removes from the run.

## External review (25 October 2026)

An external reviewer read this note. **Verdict:** sound and well evidenced
for a backend project; approve the staged experiment with N1 as a real
go/no-go point; Cranelift is the right choice for `run` and `test`, with C
kept for a later standalone build. The diagnosis is convincing, most of all
because the hand translation keeps the same representation, counting and
reuse. The reviewer's three main warnings were: tighten the speed claim,
don't derive the stack size from frame sizes, and treat the native/machine
boundary as the biggest risk.

**What changed:**
- the thesis is stated up front (§0);
- the speed claim is at least 3×, plausibly 4–8×, with 10–13× as an upper
  bound; faster than Node is not a criterion (§0, §3.4);
- "dominant avoidable cost" replaces "most of the time is interpretation"
  (§3.3), and the Cranelift prior-art sentence is narrower, with
  Haskelujah noted (§2.9);
- frame and step counters move into N1; the big stack and the full
  resource error stay in N2 (§6);
- the stack size is a generous safety margin tested against the counter,
  not computed from frame sizes (§4.3);
- a new section on the native/machine boundary recommends whole reachable
  islands (§4.6);
- N2 gets tail-call tests across calling shapes, N0 gets the three macOS
  JIT checks, and a debug allocation trace is added (§6).

## Decisions

**D1250. Build a native backend at all?** **Decided (Matt): yes, in staged
form; N1 is a stop point.**
- Context: the experiment says native code could run the `Set` benchmark
  about 10× faster than today's machine and several times faster than Node.
  But it's 8–10 lanes and a third runner to keep in step with the reference
  evaluator.
- The alternative: stay with the machine (plus route (a), 1.3–2×) and
  `run --js`.
- **Recommendation: yes**, staged, with N1's measurement as a stop point.

**D1251. Use Cranelift, in-process, rather than generating C?** **Decided
(Matt): Cranelift in-process for `run` and `test`; generating C is kept for
a later standalone build.**
- Context: C (Lean's and Koka's route) gives slightly better code, but users
  would need a C compiler when they `run`, and the Rust runtime would need a
  C interface or a C twin.
- Cranelift needs nothing installed and calls the existing Rust runtime
  directly, but no comparable language has used it yet.
- This departs from D388's "Chez text or C first". Since then, the machine
  has gained its own runtime (reuse, effects, `Delay`). Chez would rewrite
  that runtime and C would need a C twin of it; Cranelift reuses it.
- **Recommendation: yes, Cranelift.** Keep C in mind for a later
  `stitchwort build`.

**D1252. Keep the playground on the machine?** **Decided (Matt): yes.**
- Context: Cranelift can't run its code in a browser. Only a wasm backend
  (route f) would speed the playground up a lot, and that needs browser
  stack features that aren't everywhere yet. The CLI and the playground
  would then run programs on different runners.
- Both are differentially tested against the reference evaluator.
- **Recommendation: yes.** Speed the machine up modestly (route a) for the
  playground; revisit wasm when stack switching ships.

**D1253. Native code must hit resource limits at exactly the machine's
points?** **Decided (Matt): yes.**
- Context: counting frames and steps on every call, as the machine does,
  costs about 1.6 ns per call on a bare-call benchmark (about 3.5× a bare
  native call, still 17× cheaper than the machine's).
- A stack-pointer check is cheaper, but a deep program would run out at a
  different depth than on the machine. It would still be reported the same
  way, as the machine already differs from the reference evaluator.
- **Recommendation: yes, count exactly** at first. It makes the
  differential tests stronger. Revisit in tuning (N7) only if profiles show
  the counting matters.

## Appendix A: the experiments

The `set.rs` programs and the `ir` mode now live in
`bench/native/handwritten/` (a standalone cargo project; see its README and
`task native:handwritten`), built with rustc 1.99 at `opt-level=3`. There,
`set.rs` is `src/main.rs` and the no-inlining binary is `src/bin/noinline.rs`.
`micro.rs` and `micro2.rs` were not moved.

- **`set.rs`** (about 380 lines): the three versions of §3.1.
  - `uniform` uses an enum like the machine's `Value` (`Nat(u64)`,
    `Tag(u32)`, `Data(u32, Rc<[Value]>)`, `Fun(fn ptr)`), with `Bin`'s fields
    `[size, left, key, value, right]`.
  - `unpack` moves the fields out when `Rc::get_mut` succeeds and keeps the
    cell for `bin_reuse`, as `Unpack`/`CtorReuse` do.
  - `shape`, `rebuild`, `single_l/r`, `double_l/r` follow `set_nat.ir`
    line by line.
  - `insert` compares through `Value::Fun(nat_compare)`, which returns
    `Tag(LESS/EQUAL/GREATER)`.
  - `typed` is the same algorithm over
    `struct Node { size: u64, left, key: u64, right }`.
  - The program builds the keys `(i * 7919) % n`, times the insert loop and
    prints the size.
  - Built as a Cargo project with mimalloc (as the CLI uses); a second
    binary has every helper `#[inline(never)]`.
  - **`ir`** (added for D1261): the uniform insert doing what today's IR
    does. A node's cell is freed when it's taken apart on the way down,
    `shape` gets clones of both subtrees, and `rebuild`'s `Keep` makes a
    fresh node. Run as `setexp ir 1000000`.
- **`micro.rs`**: `down`/`outer`/`spin` as in `micro_call.sw` and
  `micro_tail.sw`, on `u64` with `checked_add`, using `black_box` so that
  LLVM can't compute the answers in closed form.
- **`micro2.rs`**: `down` again, plus `down_checked`, which counts steps
  and frames in a context struct against limits at every call, with a cold
  error path.
- The machine and Node timings use the `setperf` programs
  (`set_nat_1000000.sw`, `keys_nat_1000000.sw`, `micro_call.sw`,
  `micro_tail.sw`) with `/usr/bin/time -p`.

## Appendix: N1 coverage census (25 October 2026)

**[ran]** How much real code fits the N1 subset under the "whole reachable
islands" rule (§4.6). Made with `stitchwort dev opcode-census TARGET`
(hidden; `--functions` also lists every body), which lowers and compiles a
`main` exactly as `run` does and walks the bytecode. Code:
`crates/rt/src/census.rs`; the subset is one function there, `n1_blocker`.
The benchmarks are `bench/native/{set_nat,micro_call,micro_tail}.sw`
(small sizes; the real measurements scale them up). Debug build of `main`
at `acd2fae3` plus the census.

**The subset used.** The N1 row's list: `Move`, `Take`, `Drop`, `Const`,
`Call`, `TailCall`, `Return`, `Switch`, `Field`, `Unpack`, `Ctor`,
`CtorReuse`, `Test`, `JumpIfFalse`, `Jump`, and `Prim` of the `Nat`
operations. **One reading:** I took "`Nat` fast paths" to include `NatCase`,
`NatPred` and `NumSwitch`, the instructions a `Nat` pattern match lowers to.
`micro_call` and `micro_tail` cannot fit without them (Appendix A's
`down`/`spin` match on `Nat`). If N1 doesn't mean that, delete the three
lines from `n1_blocker` and rerun.

**Indirect calls.** `Apply`/`TailApply` have no static target. The census
uses a cheap closure-creation analysis rather than marking the island
"unknown": wherever a function value is made (`Closure`, `Pap`, `Global` of a
function), the target body counts as reached. A function value can only come
from such a site (or from a native, which is a blocker anyway), so every body
an `Apply` could call is in the island; it over-approximates (a value made
and never applied still counts). `Apply` itself is outside the N1 subset, so
an island with one is blocked either way; the analysis only makes the report
say what else is in the way.

**What "the entry" is.** A `main`'s entry body is glue: it builds the
`Delay` the runner steps (`Prim:Delay(Lift)`) and its `print` converts a
number (`Prim:Text(NatToText)`). So **no `main`'s whole entry island can
fit N1**, however pure the program, and the table reports the islands of the
functions the entry calls ("callee islands") and how many bodies have a
fitting island of their own.

### Benchmarks

| Program | Entry island | Callee islands that fit | Blockers |
|---|---|---|---|
| `micro_call.sw` | no (glue only) | **1 of 1** (`outer`, 2 bodies) | none in the loop; entry: `Delay(Lift)`, `Text(NatToText)` |
| `micro_tail.sw` | no (glue only) | **1 of 1** (`spin`) | none in the loop |
| `set_nat.sw` | no | 2 of 3: `foldLeft` (13 bodies) is blocked | `Global` 6 (in 3 bodies: the `Ord Nat` dictionary constants and the fold), `DropReuse` 2 (in `doubleL`/`doubleR`), `Apply` 2 (the insert's `compare` through the dictionary) |

So `micro_call` and `micro_tail` fit, and `Set` does **not**: it needs
`DropReuse`, `Global` and `Apply`, and the last two come from the `Ord`
dictionary (`insertWith` calls `compare` through it). Adding those three
makes 15 of its 16 reachable bodies fit; the 16th is the entry glue. A
specialisation pass that resolved the dictionary at lowering time would
remove `Apply` and `Global` from `Set` without N1 growing, but that is a
guess, not measured. This changes N1's plan: the stop-or-go `Set` number
cannot be measured on the subset in the stages table.

### Real programs

All ten entries are blocked. "Fit" counts bodies whose own island fits, out
of the bodies reachable from the entry (the machine inlines, so these counts
are small); "callee islands" is the entry's direct callees that fit.

| Program | Reachable bodies | Bodies with a fitting island | Callee islands fitting | Top blockers (bodies containing it) |
|---|---:|---:|---:|---|
| `Aoc.Day01.main` | 54 | 17 | 0 of 4 | Closure 14, `Text` prims 8, Captured 8, Global 8 |
| `Aoc.Day02.main` | 59 | 13 | 0 of 2 | Closure 20, Captured 17, `Effect` tail prims 12, `Text` prims 7 |
| `Aoc.Day03.main` | 54 | 16 | 0 of 4 | Closure 15, Captured 12, `Effect` tail prims 10, `Text` prims 9 |
| `Aoc.Day04.main` | 52 | 14 | 0 of 5 | Closure 11, `Text` prims 8, Apply 8, Captured 7 |
| `Aoc.Day05.main` | 65 | 19 | 0 of 4 | Closure 21, Captured 17, `Effect` tail prims 16, `Text` prims 14 |
| `Aoc.Day06.main` | 68 | 36 | 0 of 5 | Closure 12, `Text` prims 10, Captured 10, Apply 8 |
| `Aoc.Day07.main` | 69 | 21 | 0 of 5 | Closure 14, Captured 13, Apply 10, `Text` prims 9 |
| `Aoc.Day08.main` | 95 | 35 | 0 of 4 | Closure 17, Captured 12, Global 12, Apply 12 |
| `Aoc.Day09.main` | 103 | 43 | 0 of 4 | Closure 18, Captured 15, Apply 14, Global 13 |
| `Rogue.main` | 109 | 37 | 1 of 11 | Closure 26, Captured 26, Global 24, TailApply 14 |

Over the ten (bodies containing each blocker family, summed):

| Blocker | Bodies | Planned stage |
|---|---:|---|
| `Closure` | 168 | N3 (closures) |
| `Captured` | 137 | N3 |
| `Prim:Text` (`TextAppend`, `NatToText`, `TextTrim`, `TextUncons`, `TextToNat`, ...) | 97 | runtime calls |
| `Global` (a function or constant as a value) | 91 | N3 |
| `Apply` | 91 | N3 |
| `TailPrim:Effect` | 85 | N4 (effect loop) |
| `TailApply` | 75 | N3 |
| `Pap` | 53 | N3 |
| `Prim:Delay` | 44 | needed by the entry glue of every `main` |
| `Prim:Effect` | 39 | N4 |
| `Unreachable` | 12 | trivial to add |
| `Prim:Int` | 6 | runtime calls |
| `DropReuse` | 5 | small: a variant of `Unpack` |

### Reading it

- **N1 as listed covers no real program.** Every AoC `main` and the
  roguelike is blocked, mostly by closures, `Apply` and function values
  (the `Std.Effect` plumbing and `List` higher-order functions), then by
  `Text` primitives. Only 13–43 bodies per program have a pure fitting island,
  and those are leaf helpers of 1 to a few bodies.
- **Adding blockers one at a time barely helps.** The tool's `+family` lines
  (greedy; per program) show whole entries fitting only after nearly every
  family is in (10 to 12 additions). The big jumps come from the closure
  family together (`Closure`, `Captured`, `Apply`, `TailApply`, `Pap`,
  `Global`), then `Prim:Text`.
- **Highest value to add to N1, in order:** `DropReuse` (needed by `Set`;
  trivial next to `Unpack`), then `Global`, `Apply`, `TailApply` (needed
  by `Set` through the dictionary, and the first closure instructions in
  most real programs); `Unreachable` and `Prim:Int`/`Prim:Text` as runtime
  calls (cheap, so the measurement covers more programs).
- **Caveat.** The AoC `main`s are effect programs run through the effect
  runtime, so their `Effect` and `Delay` blockers are architectural (N4,
  and the runner), not a gap in the instruction list; the number to watch
  for them is the fitting-bodies column. The dev tool measures static
  presence, not time: it says nothing on how much of the run time is in the
  fitting bodies.

## Sources

Every source is linked where it is used (§2, §2.10).
- **Who checked them:** two research subagents opened the sources for this
  note.
- **Their own runs:** building Cranelift for wasm32 and clang's
  `musttail` for wasm are marked as theirs.
- **Weakest claims:** "Unison put Chez on ice" and Roc's Perceus details come
  only from secondary sources or search excerpts. They are marked so in the
  text.
- **Not found:** a published speedup of Lean's compiled code over its own
  interpreter, and any mature production functional language with a
  Cranelift backend (Haskelujah has an early one, §2.9).

Earlier notes this builds on:
- [fast-runtime.md](fast-runtime.md) (the machine, D381–D388; D388 said
  "not now" to native code, and to revisit "from the same IR");
- [effect-runtime.md](effect-runtime.md) (heap continuations, D1162);
- [partial.md](partial.md) (`Delay` and ticks);
- [stack-safe-evaluation.md](stack-safe-evaluation.md).
