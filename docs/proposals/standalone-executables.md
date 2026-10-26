# Standalone executables: `stitchwort build` with Cranelift

**Status:** design note, 25 October 2026 (SW-528, after D1286). Nothing here
changes the compiler; the experiment's code was scratch, and is kept as a
patch (Appendix A). Matt asked for the native track to go on to working
standalone executables tonight. So the decisions (D1287–D1289, [at the
end](#decisions)) are **decided by Claude, provisional**: work goes ahead on
them, and Matt can overturn any of them in review.

Claims are marked:
- **[ran]**: done for this note on the Apple M4 Pro (macOS 26, arm64),
  Cranelift 0.136.2 as pinned in `crates/native`, clang 21.1.8 and ld64-956.6.
  The machine was heavily shared (load average 40–56), so the times are rough.
- **[source]**: read in this repository at `98a10391`.
- **[web]**: read in the linked page or source file. A research subagent
  opened the external sources. Where it could only see a search excerpt, the
  claim says so.
- **[inferred]**: my reasoning, not tested.

## 0. Summary

**The goal.** `stitchwort build --native games/rogue -o rogue` writes an
executable that plays the roguelike with no `stitchwort` binary, no source and
no compiler: a normal Mach-O or ELF file.

**The shape** (recommended):

```
stitchwort build  ──►  program.o   (generated: the lowered program as data,
                                    plus, with --native, the compiled
                                    functions, made by cranelift-object)
                   +   libstitchwort_standalone.a   (prebuilt from the
                                    workspace: values, the machine, the
                                    runner, the host: console, raw mode,
                                    random, errors, limits; C `main`)
                   ──►  cc program.o libstitchwort_standalone.a -o rogue
```

**What the experiment showed [ran].** One N1-compiled program (`micro_call`,
20 million calls) was written to an object file with `cranelift-object`,
linked by the system `cc` against a static library built from `crates/rt`,
and run standalone:
- It printed the right answer (`20000000`) with the machine's step count
  (22,000,000).
- It took 0.13 s, against 0.32–0.37 s for `stitchwort run --native`, which
  also checks the program first.
- The link took 0.16 s. The stripped binary is 586 KB. With the whole machine
  and runner linked in as well, it is 735 KB.
- `is_pic` must be on. A non-PIC object linked with warnings and died with
  `SIGBUS`.
- The linker signed the binary ad hoc by itself, and `strip` kept a
  signature. With the signature removed, macOS killed the binary (exit 137).

**The key finding for the plan.** The roguelike can't run natively yet. By
the census, none of its code islands fits today's compiled subset, and it
needs closures (N3) and effects (N4) to fit (§3). But a standalone
executable doesn't need native code to exist. The **hybrid** (§3.3) gives a
binary that plays the roguelike in three lanes, before N3 and N4, and
without touching the native code generator:
- it embeds the lowered program and runs it on the machine;
- it compiles whichever islands fit, from the same build;
- as N3 and N4 land, more of the program is compiled, until all of it is.

This is the same rule `run --native` already follows (whole reachable
islands, the machine running the rest), so it adds no new boundary.

**Plan** (§9): seven lanes in two tracks.
- **Track 1** (parallel with N2a, now):
  - S1, a codec for the lowered program;
  - S2, the host in its own crate;
  - S3, the runtime library and `stitchwort build`.
  - **Milestone M1:** `stitchwort build games/rogue` plays.
- **Track 2** (after N2a):
  - S4, a code generator free of host addresses;
  - S5, object output and `build --native`;
  - S6, every pure primitive through the runtime.
  - Then N3 and N4, each with a standalone test.
  - S7, the roguelike fully native.
  - **Milestone M2:** `stitchwort build --native games/rogue` plays, with
    every function the entry reaches compiled.

**Decisions** (all decided by Claude, provisional):
- **D1287:** the hybrid is the architecture, not a stopgap.
- **D1288:** the binary carries the lowered program, not source and a
  checker.
- **D1289:** linking uses the system `cc`, against a prebuilt runtime
  library; no cargo, no bundled linker.

## 1. Object output

### 1.1 `cranelift-object` exists, in our release train

- **The crate:** `cranelift-object` 0.136.2 was published on 2 October 2026,
  with 0.136.3 and 0.136.4 after it
  ([crates.io versions](https://crates.io/api/v1/crates/cranelift-object/versions))
  **[web]**. It is in lockstep with the five Cranelift crates `crates/native`
  pins at `=0.136.2` **[source]**. It depends on `object` ^0.40
  ([dependencies](https://crates.io/api/v1/crates/cranelift-object/0.136.2/dependencies))
  **[web]**.
- **Formats:** ELF, Mach-O and COFF, chosen from the target triple of the
  ISA. Wasm and unknown formats are errors. The architectures are x86,
  x86-64, Arm, AArch64, s390x, and riscv64 (ELF only)
  ([backend.rs at release-49.0.0](https://raw.githubusercontent.com/bytecodealliance/wasmtime/release-49.0.0/cranelift/object/src/backend.rs))
  **[web]**.
- **Data:**
  - `declare_data` and `define_data` place zero-filled data in `.bss`,
    writable data in a data section, and read-only data in a constant
    section.
  - Pointers inside data are `Abs8` relocations.
  - Thread-local data is supported on ELF and Mach-O (same file) **[web]**.
- **One trap:** the `unwind_info(true)` builder option panics in `finish` for
  Mach-O ("not yet implemented", same file) **[web]**. Leave it off. Native
  frames don't unwind (errors are returned, §4.6 of
  [native-compilation.md](native-compilation.md)), so nothing needs unwind
  tables.

### 1.2 `is_pic` must be on

- **What `is_pic` changes:** on aarch64, `is_pic = true` loads every outside
  symbol through the GOT. With `false`, far symbols become absolute 64-bit
  relocations inside the code
  ([inst.isle](https://raw.githubusercontent.com/bytecodealliance/wasmtime/release-49.0.0/cranelift/codegen/src/isa/aarch64/inst.isle))
  **[web]**.
- **Why that breaks:** wasmtime#5544 records that an absolute relocation in
  the text section "causes the dynamic linker to crash on macOS as the text
  segment is read-only"
  ([#5544](https://github.com/bytecodealliance/wasmtime/issues/5544))
  **[web]**.
- **What `rustc_codegen_cranelift` does:** `is_pic = true` for objects and
  `false` for its JIT
  ([cg_clif lib.rs](https://raw.githubusercontent.com/rust-lang/rustc_codegen_cranelift/master/src/lib.rs))
  **[web]**.
- **What the experiment saw [ran]:**
  - Non-PIC: the object had 14 `ARM64_RELOC_UNSIGNED` relocations in
    `__text`, one per helper call. `ld` warned "alignment (4) of atom
    `_sw_body5` is too small", and the binary died with `SIGBUS`.
  - PIC: `GOT_LOAD_PAGE21` and `GOT_LOAD_PAGEOFF12` pairs, no warnings, and
    it ran.

### 1.3 The old arm64 macOS bug

[native-compilation.md](native-compilation.md) §2.10 used wasmtime#4564, an
open arm64 Darwin relocation bug, as a reason to JIT rather than write `.o`
files.
- **Its status:** still open. It failed on Cranelift 0.86 with a call
  relocation whose addend was −4
  ([#4564](https://github.com/bytecodealliance/wasmtime/issues/4564))
  **[web]**.
- **Today's code:** it emits `Arm64Call` with addend 0
  ([emit.rs](https://raw.githubusercontent.com/bytecodealliance/wasmtime/release-49.0.0/cranelift/codegen/src/isa/aarch64/inst/emit.rs))
  **[web]**.
- **Other projects:** `rustc_codegen_cranelift` lists macOS AArch64 as
  "Fully supported and tested"
  ([README](https://github.com/rust-lang/rustc_codegen_cranelift)) **[web]**.
- **Our object:** it has `BR26` calls between bodies, and it linked and ran
  **[ran]**.

So the bug looks obsolete. It is not a reason against objects any more.

### 1.4 What changes in the N1 code generator

The N1 compiler (`crates/native/src/n1.rs`) has four JIT-specific parts
**[source]**:

| JIT today | In an object |
|---|---|
| `JITModule`, with `MAP_JIT` memory on macOS arm64 (`map_jit.rs`) | `ObjectModule`. No executable memory at run time, so `MAP_JIT` and the W^X dance go; the loader maps `__text` |
| Runtime helpers (`sw_ctor`, `sw_prim`, …) resolved by `JITBuilder::symbol(name, address)` | The same `Linkage::Import` declarations, resolved by the linker. The helpers need `#[unsafe(no_mangle)]` so that their symbol names are `sw_ctor` and so on (they are mangled today) |
| **Host addresses as immediates** (`Gen::address`): constant-pool values (`Const` of a text or big number), each `PrimOp` (`op_address` boxes one per use), each `ApplyCache`, `&program.shapes`, `NumSwitch` tables | Not valid in another process. See below |
| The function table (`Context::functions`) and root trampolines, filled from `get_finalized_function` | A data object `sw_functions` (one pointer per global, written with function relocations) and exported trampolines |

**Host addresses: make the code take them from the context [inferred].**
`Context` gains one field, `tables: *const Tables`, built by the runtime when
the run starts. `Tables` holds pointers to:
- the image's constant pool (`Const k` becomes a load of
  `tables.pool + 24·k`);
- `program.shapes`;
- the image's `num_tables`;
- an operations table (`PrimOp`s by index, numbered by the compiler and
  recorded in the program);
- an `ApplyCache` array of a count the compiled module declares.

Then:
- **One code generator for both.** The JIT gets the same tables, so there is
  only one code generator, and every N1 test covers the code that goes into
  objects.
- **The cost** is one load per function to get the table pointer (keep it in
  a variable), on paths that already call into the runtime.

The alternative is symbols for each item, with the data built into the
object. It doesn't work for the pool: its values (`Text`, `BigNat`, closures
like `DoneK`) are `Rc` cells that the runtime must create.

**The tables must match the code's numbering [inferred].** The runtime
rebuilds the image from the embedded program with `code::compile`, so the
pool and table indices baked into the object must be the ones that
recompilation produces.
- `code::compile` is deterministic, and the library and the CLI come from
  one workspace build.
- The object records a hash of the encoded image, and the runtime checks it
  at start-up. A mismatch is an internal error, never a silent miscompile.

**Leaves no trace in the language.** None of this is visible to programs.

## 2. The runtime a binary links

### 2.1 What it contains

The standalone binary is the `stitchwort run` path minus the front end
**[source]**:

| Piece | Where today | In the binary |
|---|---|---|
| `Value`, cells, drops, the freeing work list, big numbers (`num-bigint`) | `crates/rt` (`value.rs`, `prims.rs`) | As is |
| The machine and its bytecode compiler | `machine.rs`, `code.rs` | As is: it runs the entry glue and every function that isn't compiled (§3.3) |
| The runner: `Delay` stepping, ticks, effect routing, `perform` for the host operations | `run.rs` | As is: `run_main_native` |
| Native helpers | `native_abi.rs` | As is, with exported names (§1.4) |
| `print`, `readLine`, `readAll`, `readBytes`, `write`, `randomSeed` | `host.rs`, generic over `BufRead`/`Write`; the seed from `std`'s `RandomState` | As is |
| `console` and `keysMode`: raw mode, alternate screen, the restore guard, the signal thread | `crates/cli/src/terminal.rs` (needs `nix`; `crates/rt` is also built for wasm, so it can't have them) | **Moves** to a new crate, `crates/host`, used by the CLI and the binary (S2) |
| The big stack | `driver::with_stack`, `NATIVE_STACK` (4 GiB) in `crates/cli/src/main.rs` | The binary's `main` starts the run on the same kind of thread; the constant moves to `crates/host` |
| mimalloc | `#[global_allocator]` in the CLI | The same, in the library |
| Error reporting and limits | `RunError::diagnostic` needs `main`'s source span; `Limits::from_core` | §2.4 |

Not in the binary: the parser, the elaborator, the kernel, the checker's
cache, the JS backend, Cranelift. `crates/rt` depends on `stitchwort-core` and
`stitchwort-syntax` for a few types (`ResourceError`, the native operation
enums, `Diagnostic`). The linker keeps only what is reached.

### 2.2 Static library or a generated cargo crate

**Option A: a static library, linked by the system `cc` (recommended).**
- A new crate, `crates/standalone` (`crate-type = ["staticlib"]`), defines
  C `main`. The generated object provides the program (§4) and, with
  `--native`, the code.
- **[ran]**:
  - The library built from scratch (rt, core, syntax, num-bigint, mimalloc,
    `lto = true`, `codegen-units = 1`, `panic = "abort"`) in about 10 s of
    cargo time. That cost falls when the workspace is built, not when a
    user runs `build`.
  - The `.a` is 6.7–7.0 MB. Linking from it takes 0.16 s.
  - With `-Wl,-dead_strip` and `strip`, binaries are 586 KB (compiled code
    and helpers only) and 735 KB (the machine and runner linked as well).
    So the machine costs about 150 KB.
  - `rustc --print native-static-libs` gave `-lSystem -lc -lm` on macOS. The
    library's build records its own list for the link line.
- **User needs:** a C toolchain, which is Xcode's command line tools on
  macOS, or `cc` on Linux.

**Option B: generate a small Rust `main` crate and call cargo.**
- **User needs:** rustc, cargo and the runtime's source (or a registry) on
  their machine.
- **First build:** like the scratch library's, about 10 s of compilation
  plus cargo's start-up (26 s wall through `nix develop` here) **[ran]**.
  Later builds are faster only if a target directory is kept per user.
- **What it gains:** nothing at run time; it is the same code.
- **It is route (e)** of the native note, which was rejected for `run` for
  the same reasons.

**Rejected:** B. It needs a Rust toolchain at `build` time and costs tens of
seconds, where A needs a C linker and costs a fraction of a second.

**Where the `.a` comes from.**
- The CLI looks for `libstitchwort_standalone.a` next to its own executable,
  then in `../lib/stitchwort/`. The environment variable
  `STITCHWORT_RUNTIME` overrides both.
- `cargo build --release -p stitchwort-cli -p stitchwort-standalone` puts
  both files in `target/release/`.
- The Nix package installs the library under `lib/stitchwort/`.
- Embedding the 7 MB archive in the CLI with `include_bytes!` would need the
  library built before the CLI. Cargo's artifact dependencies, which do
  that, are unstable. So: a file beside the CLI.

### 2.3 Which linker

| Linker | For | Against |
|---|---|---|
| **System `cc`** (clang on macOS, which calls ld64; gcc or clang on Linux) | Already there for any developer. On macOS it signs arm64 executables by itself (§6.2). Every Cranelift AOT toolchain found links this way (§8) | Users need a C toolchain |
| `rust-lld`, which rustup ships | Rust 1.90 links `x86_64-unknown-linux-gnu` with it by default ([Rust blog](https://blog.rust-lang.org/2025/09/01/rust-lld-on-1.90.0-stable)) **[web]** | Only users who have rustup have it. Whether it is used for Apple targets wasn't confirmed |
| lld (Mach-O, ELF), bundled | "Drop-in replacement for … ld64" ([lld docs](https://lld.llvm.org/MachO/index.html)) **[web]**; it signs arm64 by default (`-adhoc_codesign`, [Options.td](https://raw.githubusercontent.com/llvm/llvm-project/main/lld/MachO/Options.td)) **[web]**. Roc's Zig compiler embeds LLD for this reason ([linker.zig](https://raw.githubusercontent.com/roc-lang/roc/main/src/cli/linker.zig)) **[web]** | A large C++ dependency in the CLI and a Nix build to follow: the cost the native note gave for rejecting LLVM |
| `zig cc` | Cross-links easily; Wasmer's `create-exe` uses it ([Wasmer](https://wasmer.io/posts/wasm-as-universal-binary-format-part-1-native-executables)) **[web]** | Another outside tool |

**Recommendation (D1289): the system `cc`.** It finds `$CC`, else `cc`. Its
arguments are:
- the object and the library;
- the recorded native libraries;
- `-Wl,-dead_strip` on macOS, or `-Wl,--gc-sections` on Linux;
- `-o out`.

If `cc` is missing, `build` says so and names the package to install.
Bundling lld can come later if users without a C toolchain matter.

### 2.4 Errors and limits in the binary [inferred]

- **Limits:** the build embeds the `Limits` that `stitchwort run` would use for
  the project (steps, frames). The binary enforces them exactly as `run` does
  (D1253 holds: the same counters, machine or native). There are no
  command-line flags for them.
- **Errors:**
  - `RunError::diagnostic` points at `main`'s source, which the binary
    doesn't have. Instead, the binary prints the same code and message
    without the excerpt, for example `error[E-RESOURCE]: ran out of
    resources: …`.
  - The deep-recursion report still works, because function names are in the
    program.
  - `Fail` prints `error: <msg>`.
  - Exit statuses are `stitchwort run`'s.
- **Panics:** `panic = "abort"` would skip the restore guard. So the library
  keeps `panic = "unwind"`, like the CLI (terminal-io.md §5), and only the
  experiment used abort.

## 3. What must be compiled

### 3.1 The census of the roguelike **[ran]**

`stitchwort dev opcode-census Rogue.main` (debug build of `98a10391`):
- 245 bodies are reachable, of 460 in the image; 152 are blocked.
- 88 bodies have an island of their own that fits.
- **0 of the entry's 2 callee islands fit**, so today `run --native` runs
  the whole roguelike on the machine.

The blockers:

| Blocker family | Occurrences, bodies | Which stage covers it |
|---|---|---|
| `Captured` | 281, 99 | N3 (closures) |
| `Closure` | 200, 81 | N3 |
| `Pap` | 19, 8 | N3 |
| `TailPrim:Effect` (`Bind`) | 51, 51 | N4 (effects) |
| `Prim:Effect` (`Bind` 64, `Translate` 5, `FoldIn` 2, `RunPure` 1) | 72, 32 | N4 |
| `Prim:Delay` (`BindD`, `Now`, `Lift`, `MapSig`, `FoldD`, `Pfix`) | 86, 50 | **already computable through `sw_prim`** (below) |
| `Prim:Text` (`TextAppend`, `NatToText`, `TextFromList`, `TextToList`, `TextJoin`) | 122, 16 | **already computable through `sw_prim`** |

The tool's greedy line confirms the entry island fits only when all seven
families are in.

**A cheap find [source].**
- **What the machine does:** it runs every `Prim` except the effect
  operations and `Text.fold` through `prims::eval` (`machine.rs`, the `Prim`
  arm). That includes the `Delay` constructors, which only build a value
  (`prims.rs`: `Primitive::Now => Value::Delay(…)`).
- **What native code already has:** N1's `sw_prim` helper calls
  `prims::eval` for any operation.
- **What is left:** these families are blocked only by
  `census::n1_blocker`'s list. Admitting them is a small change (S6),
  which leaves closures and effects as the real gaps.

### 3.2 Fully native: what it would take

The roguelike runs wholly natively only after N3 and N4 (and S6). Even
then, "no bytecode" isn't quite the architecture **[source]**:
- `main`'s entry body is glue that the machine runs: it builds the `Delay`
  that the runner steps.
- The runner (`run.rs`) is Rust: it steps that `Delay`, routes operations and
  performs `IO`.
- Constants (`Global`) share the machine's cache through `NativeRun`.

Removing the machine altogether would mean compiling the entry glue, and
giving the runner a native way to call continuations. N4 builds the second
part. The machine costs about 150 KB (§2.2), so there's no reason to remove
it. "Fully native" here means **every body the entry reaches is compiled**,
which `--verbose` can report.

### 3.3 The hybrid

**What it is.** The binary embeds the lowered program and links the machine.
At start-up it rebuilds the bytecode image and runs `run_main_native` with a
factory that returns the linked native islands (an `AotIslands`, the
counterpart of `n1::Islands`), or none:
- **With no compiled code** (`build` without `--native`, or nothing fits),
  the binary is `stitchwort run` for one program: the machine runs
  everything.
- **With compiled islands**, exactly what `run --native` does happens
  (native-compilation.md §4.6): whole reachable islands, entered from the
  entry body. There is no per-function mixing, so no new boundary rules,
  counting rules or tail-call questions.

**Why it is the quickest path to a standalone game.**
- **It needs none of N2–N4.** The machine already runs the roguelike, with
  partial code, handlers and the terminal.
- **It is three lanes** (S1–S3), none of which touches `n1.rs`. That's where
  N2a is working now, so they can run in parallel with it.
- **It removes the effort, not just the delay.** Every later native stage
  makes the same binary faster, with no change to how it is built.

**Its honest costs:**
- **Speed:** until N3 and N4 land, the roguelike runs at machine speed in
  the binary. For a turn-based game that waits on key presses, this doesn't
  matter. A piped four-key game under `stitchwort run`, checking included,
  took 1.4 s wall on the loaded machine **[ran]**. The per-turn share wasn't
  measured; S7 measures it.
- **Coverage only grows per whole island.** With only N1–N2, a real program
  has few islands that fit (the census: leaf helpers only). The hybrid
  doesn't change that; N3 and N4 do.
- **Two executors in one binary:** that's already true of `run --native`,
  and the differential tests cover it.

**Rejected variant: per-function mixing.** Native code could call the
machine for functions that don't compile. This would make more of the
roguelike native before N3 and N4. The native note rejected it for good
reasons: a nested `run` on the Rust stack, `Ret` kinds with no native
counterpart, and a boundary rule for every question (§4.6 there). N3 and N4
are approved and next, so it would be work that is thrown away.

**Rejected variant: embed the source and the checker.** The binary would
contain the whole compiler and check the program at start-up.
- **Size:** the release CLI with `native` is 18.4 MB **[ran]**.
- **Start-up:** `check --no-cache` of the roguelike took 7.2 s wall, or
  3.5 s user under load **[ran]**. That would be paid on the first run, or
  a cache would have to be shipped with the binary.

Carrying the lowered program instead (D1288) costs one codec (S1).

## 4. How the program gets into the binary

- **What is serialised:** S1 writes a codec for `stitchwort_rt::ir::Program`,
  the lowered and optimised program that `lower_main` returns **[source]**.
  It is a plain tree: globals, lambdas, type and constructor names, `Expr`,
  literals (`BigUint`, `BigInt`, `Rc<str>`), `PrimOp`s, `MainRow`, `Shapes`.
  It includes no `Term`, no closures and no pointers. The model for the
  codec is the check cache's hand-written codec
  (`crates/elab/src/cache/codec.rs`): a version byte, then LEB128 integers,
  with no new dependency.
- **What isn't serialised:** the bytecode image. The runtime rebuilds it
  with `code::compile`. That keeps `Value` out of the format, since the pool
  holds `Rc` values like `DoneK`. The cost is milliseconds **[inferred]**.
- **Where it lives:** the encoded program and the limits are a read-only
  data symbol, `sw_program`, with its length in `sw_program_len`.
- **How the object is written:**
  - Without `--native`, it is written with the `object` crate, the same
    major version `cranelift-object` uses, so that `build` doesn't need the
    `native` Cargo feature.
  - With `--native`, the data goes into the same `ObjectModule` as the code.

## 5. Erasure and proofs

**Nothing proof-related is needed at run time [source].**
- **`lower_main` erases first:**
  - Definitions whose type is a proposition or a type former are dropped.
  - Erased parameters are dropped from calls, and lambdas get
    `Expr::Erased` for them.
  - Matches on proofs keep their only branch.
  - Definitions by `decreasing` run their run bodies
    ([core.md, "Erasure and JS extraction"](../core.md); `crates/rt/src/erasure.rs`).
- **The IR has no terms:** `Program` holds no `Term` and no kernel value, so
  the binary can't contain a proof.
- **Theorems aren't reachable:** the roguelike's `Rogue.Proofs.*` and its
  tests aren't reachable from `Rogue.main`, so they aren't in the program.
- **What is left of proofs** is `Value::Erased`, a placeholder in argument
  slots that a function value must still be passed. It's one word per such
  argument, with no code.
- **Native operations that take proof arguments** (`DivFuel` and
  `EqNatSound`, arity 3) receive `Erased` for them and never look at it.

A related point: the binary also doesn't re-check anything. It trusts that
`build` checked the program, as `run` does today.

## 6. Effects at the top level

### 6.1 `main`'s `IO`, `Terminal` and `Random`

**[source]** (`games/rogue/src/Rogue/Rogue.sw`):
```
def main(): {IO, Partial} () :=
  let seed := IO.randomSeed() % 2147483648
  IO.print (ending (playOn seed))
def playOn (seed: Nat): {IO, Partial} State :=
  Terminal.toIO (() => seeded seed (() => playGame (newGame())))
```

- **`Random` and `Terminal` are handled by Stitchwort code.**
  - `Rogue.seeded` is a handler in the game.
  - `Terminal.toIO` is a std handler that interprets `Terminal` into `IO`
    operations: `console`, `keysMode`, `readBytes`, `write`.

  They are ordinary functions in the program, so they run on the machine or
  compiled, like any other code.
- **Only `IO` (and `Partial`'s ticks) reach the runner.** `Runner::perform`
  (`run.rs`) does `print`, `readLine`, `readAll`, `console`, `keysMode`,
  `readBytes`, `write` and `randomSeed`. It is in the library, unchanged.
- **The host behind it:**
  - `console` and `keysMode` go through the `host::Terminal` trait, whose
    Unix implementation moves to `crates/host` (S2).
  - Standard input is a locked `BufRead` and output a `BufWriter`, as in
    `run_main`.
  - `randomSeed` is `host::random_seed`.
- **Putting the terminal back:** the binary's `main` does what the CLI's
  does for `run`:
  - `catch_signals()` before any thread starts;
  - the run on the big-stack thread;
  - the `Restore` guard and the panic hook from `crates/host`.

  So Ctrl-C, `Fail`, `E-IO`, a resource error and a panic all restore the
  terminal (terminal-io.md §5). The CLI's pseudo-terminal test
  (`crates/cli/tests/keys_mode.rs`) gets a twin for the binary.
- **Under N4:** once effects are compiled, the effect loop calls compiled
  continuations. That's in N4's scope for `run --native` and changes
  nothing here.

## 7. Targets, cross-compilation and signing

### 7.1 Targets

- **Cranelift's targets:**
  - "Cranelift is a cross-compiler, so the ISA to target can be selected
    dynamically", with `isa::lookup(triple)`
    ([cranelift_codegen::isa](https://docs.rs/cranelift-codegen/0.136.2/cranelift_codegen/isa/index.html))
    **[web]**.
  - The backends are x86-64, aarch64, s390x and riscv64
    ([README](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/README.md))
    **[web]**.
  - The calling conventions include SystemV, WindowsFastcall and
    AppleAarch64
    ([CallConv](https://docs.rs/cranelift-codegen/0.136.2/cranelift_codegen/isa/enum.CallConv.html))
    **[web]**.
- **Cross-compiling is not just Cranelift [inferred].** Writing a Linux
  x86-64 object on a Mac is easy: use `isa::lookup` instead of
  `cranelift_native`. But the binary also needs:
  - the runtime library built for that target (a Rust cross build);
  - a linker for it.
- **Out of scope:** this plan builds for the host only. A `--target` flag
  can come later, with libraries per target and probably `zig cc` or lld as
  the linker.
- **Supported hosts for this plan** (`n1::SUPPORTED_TARGETS`; as of NO7 of
  native-only.md, 26 October 2026):

  | Host | Object | Status | Evidence |
  |---|---|---|---|
  | macOS arm64 | Mach-O, signed by the linker | tested | every tier, on the M4 Pro |
  | Linux aarch64 | ELF | tested | NO7: the `native` lane and every `build` test, natively in a NixOS VM, under overcommit modes 0 and 1 |
  | Linux x86-64 | ELF | tested under emulation | NO7: the same tests through Rosetta in that VM; all pass but `link_failures_are_explained`, which Rosetta's `posix_spawn` breaks. Not run on x86-64 hardware |
  | macOS x86-64 | Mach-O | untested | no Intel Mac |
  | Windows | COFF | unsupported | see below |

  On Linux the executable links the C library dynamically, so it runs
  where the loader it names exists (a nix devShell's links the nix store's
  `ld-linux`); a static or musl link, for one binary across distributions,
  isn't done.
- **Windows:** COFF objects are supported, but the terminal host is Unix
  only (`cfg(unix)`), as for `run`.
- **Constraints on the code:**
  - Objects must be built with `preserve_frame_pointers`, as the JIT is,
    since `return_call` needs it on x86-64 (N0).
  - The `tail` calling convention works the same in objects.

### 7.2 macOS code signing

- **The requirement:** "on Macs with Apple silicon, and starting in macOS
  Big Sur 11 beta 6, the operating system enforces that any executable must
  be signed … a simple ad-hoc signature is sufficient"
  ([Apple, Big Sur release notes](https://developer.apple.com/tutorials/data/documentation/macos-release-notes/macos-big-sur-11_0_1-universal-apps-release-notes.md))
  **[web]**.
- **Who signs:**
  - The same notes say that since Xcode 12 the toolchain signs executables
    built with `clang` or `ld` at link time.
  - Tools that change a binary afterwards (`strip`, `install_name_tool`)
    need `codesign` again.
  - Ad-hoc-signed binaries "cannot pass through Gatekeeper" **[web]**.
- **What failure looks like:** an unsigned binary is killed with
  `SIGKILL (Code Signature Invalid)`
  ([Apple developer forums](https://developer.apple.com/forums/thread/732767))
  **[web]**.
- **What the experiment saw [ran]:**
  - `codesign -dv` on the linked binary showed `flags=0x20002(adhoc,linker-signed)`,
    from both the Nix clang wrapper's `ld` and `/usr/bin/cc`.
  - After `strip -o`, the output was still signed ad hoc, and it ran.
  - After `codesign --remove-signature`, running it gave exit status 137,
    which is `SIGKILL`.
- **So `build` needs no signing step of its own when it links with `cc`.**
  - If `build` ever strips or patches a binary after linking, it must run
    `codesign -s - -f` again.
  - S3's test checks `codesign -v` on macOS.
  - A bundled lld also signs by default (§2.3).
- **What changes from the JIT:** there is no executable memory at run time,
  so the `MAP_JIT` and hardened-runtime questions of N0 don't arise. A
  hardened or notarised build would need a Developer ID and a real
  signature. That is a distribution question for later.

## 8. Code quality, and prior art

### 8.1 Cranelift against LLVM and C compilers

The published measurements are few and indirect. **No source found measures
Cranelift against LLVM on native, non-wasm code of the kind we generate.**

| Source | What it measured | Result |
|---|---|---|
| Cranelift README, citing Xu & Kjolstad, *Copy-and-Patch Compilation* (OOPSLA 2021), Fig. 22 | wasm: Wasmtime 0.26 against WAVM (LLVM) and V8, CoreMark and PolyBench | "~2% slower than V8 (TurboFan), ~14% slower than WAVM (LLVM)"; compiles about 10× faster ([README](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/README.md), [paper](https://arxiv.org/abs/2011.13127)) **[web]**. The 14% is read off a bar chart; not confirmed from the text |
| Engelke & Schwarz, CGO 2024 | database query compilation | "Cranelift achieves a similar run-time performance to unoptimized LLVM, but compiles just 20–35% faster"; "LLVM achieves the highest execution performance" ([abstract](https://2024.cgo.org/details/cgo-2024-main-conference/9/Compile-Time-Analysis-of-Compiler-Frameworks-for-Query-Compilation)) **[web, abstract only]** |
| TPDE (arXiv 2025) | wasm and SPEC CPU2017 | Indirect: Cranelift's code was 1.64× faster than TPDE's on wasm, and TPDE's code was roughly LLVM -O0, 1.5–1.8× slower than -O1 ([paper](https://arxiv.org/html/2505.22610)) **[web]** |
| Fallin, regalloc2 (2022) | Cranelift against itself | 10–20% faster code on register-heavy benchmarks ([blog](https://cfallin.org/blog/2022/06/09/cranelift-regalloc2/)) **[web]** |
| Wasmer's benchmarks | wasm, Cranelift against LLVM backends | Cranelift 2.5–4.6× native, LLVM 1.2–2.1× **[search excerpt only; the page returned 403]** |

**What this means here [inferred].**
- **The gap varies a lot.** It runs from LLVM's code being 14% faster to it
  being about 2× faster, depending on the workload. It is largest where
  LLVM's loop and inlining passes have work to do.
- **Our generated code is mostly not that.** It is calls, tag tests, loads
  and stores of three-word values, reference counts and runtime calls
  (native-compilation.md, "The miss investigated").
- **Measured costs are elsewhere.** The `Set` profile's costs were the
  allocator (34%) and the code's shape (registers in memory, counting),
  which N2a is fixing. Instruction selection wasn't among them.
- **The hand-translated Rust bounds it.** It was compiled by LLVM and did
  the IR's work, and it was about 5× the machine, where N1 was 3× (same
  note). That gap is mostly code shape, not LLVM.
- **So code quality is not why to pick a backend now.** Standalone builds
  use the same Cranelift code as `run --native`, so they're exactly as fast
  as the JIT, minus the JIT's compile time.
- **A later option, not a pivot:** if profiles ever show instruction
  selection mattering, an LLVM or C path could be added for `build --release`
  from the same bytecode, with the same runtime library. Nothing in this
  plan closes that off.

### 8.2 How others ship executables with Cranelift

- **`rustc_codegen_cranelift`:**
  - It makes one `ObjectModule` per codegen unit
    (`ObjectBuilder::new(isa, name + ".o", …)`), with `is_pic = true`
    ([aot.rs](https://raw.githubusercontent.com/rust-lang/rustc_codegen_cranelift/master/src/driver/aot.rs))
    **[web]**.
  - It leaves linking to rustc's ordinary linker invocation: it doesn't
    override `CodegenBackend::link`
    ([backend.rs](https://raw.githubusercontent.com/rust-lang/rust/master/compiler/rustc_codegen_ssa/src/traits/backend.rs))
    **[web]**.
  - It is the closest model: Cranelift objects, a runtime as a library
    (`std`), and the system linker.
- **saltwater** (a C compiler, archived): `cranelift-object` with
  `is_pic`, linked by running `cc`
  ([lib.rs](https://raw.githubusercontent.com/jyn514/saltwater/master/saltwater-codegen/lib.rs))
  **[web]**.
- **Wasmer `create-exe`:** links a native `.o` with "a minimal libwasmer.a
  (headless, with no compilers)", using Zig or Clang
  ([Wasmer, 2022](https://wasmer.io/posts/wasm-as-universal-binary-format-part-1-native-executables))
  **[web]**. The post doesn't say which compiler made the object. The shape
  is ours: generated object, runtime library with no compiler, system or
  bundled linker.
- **Wasmtime `compile`:** writes `.cwasm`, an ELF-format artefact that
  `wasmtime` loads. It is not a standalone executable
  ([CLI docs](https://docs.wasmtime.dev/cli-options.html)) **[web]**.
- **Roc** (not Cranelift):
  - Its Rust-era "surgical linker" patched a prebuilt host, ELF only
    ([README](https://raw.githubusercontent.com/roc-lang/roc/alpha4-rolling/crates/linker/README.md)).
  - Its Zig rewrite embeds LLD and re-signs Mach-O ad hoc itself
    ([linker.zig](https://raw.githubusercontent.com/roc-lang/roc/main/src/cli/linker.zig))
    **[web]**.
  - It shows what a bundled linker costs: you then own signing.
- **The pattern everywhere:** a runtime as a static library (or the
  platform's), linked by the system linker or an embedded lld. Nobody found
  ships a cargo build at user build time.

## 9. The staged plan

The order relative to the native stages:

```
now:        N2a (doing) ─────────────┐
            S1 codec ─┐              │
            S2 host ──┼─► S3 build ══► M1: `stitchwort build games/rogue` plays
                      │              │
after N2a:            └──────────────┴─► S4 relocatable code ─► S5 objects, build --native
                                         N2b (parallel with S4/S5)
            S6 pure prims via sw_prim (after S4)
            N3 closures (+ standalone test) ─► N4 effects (+ standalone test)
            S7 roguelike fully native ══► M2: `stitchwort build --native games/rogue`
```

Each stage is one lane. Every lane runs only named tests within the test
tiers. The program fixtures are `bench/native/*.sw`, `games/rogue`, and a
small IO program written in S3.

**S1. A codec for the lowered program.**
- **Files:**
  - new `crates/rt/src/codec.rs`, with
    `pub fn encode(program: &Program, limits: &Limits) -> Vec<u8>` and
    `pub fn decode(bytes: &[u8]) -> Result<(Program, Limits), CodecError>`;
  - exports in `crates/rt/src/lib.rs`.
- **The format:** a magic number, a format version, and the
  `CARGO_PKG_VERSION` plus a build hash (refuse others). Then LEB128
  integers and length-prefixed strings, in the style of
  `crates/elab/src/cache/codec.rs`. Every `ir` type gets a tag byte per
  variant.
- **Tests** (`crates/rt/tests/codec.rs`):
  - round-trip `micro_call`, `micro_tail`, `set_nat`, an effects program and
    `Rogue.main`;
  - `code::compile(decode(encode(p)))` must give the same image as
    `code::compile(p)`. Compare `pretty` listings, or add `PartialEq` on
    `Image`.
  - `run_main` of the decoded program prints the same output on a scripted
    input;
  - truncated or corrupted bytes give `Err`, not a panic.
- **Done when:** these pass, and the encoded size of `Rogue.main` is
  recorded in the commit message.

**S2. The host in its own crate.**
- **Files:**
  - new `crates/host` (`stitchwort-host`, depending on `stitchwort-rt` and
    `nix` with the same features as today);
  - `crates/cli/src/terminal.rs` moves there whole: `UnixTerminal`,
    `Restore`, `catch_signals`, the panic hook, `wait_for_node` stays in the
    CLI if it's Node-specific;
  - add `pub const NATIVE_STACK` and `pub fn with_stack` (moved from
    `driver::with_stack`'s body, which then calls it, or duplicated: decide
    in the lane);
  - the CLI uses the crate.
- **Tests:** the existing `crates/cli/tests/keys_mode.rs` and `run.rs`
  tests named in the lane, unchanged and passing. No behaviour change.
- **Done when:** the CLI builds on the new crate and those tests pass.

**S3. The runtime library and `stitchwort build` (machine only). Milestone
M1.**
- **Files:**
  - new `crates/standalone` (`stitchwort-standalone`, `crate-type =
    ["staticlib", "rlib"]`, release profile with `lto`; keep
    `panic = "unwind"`). It provides C `main`, which:
    1. installs `catch_signals`;
    2. reads `sw_program` and `sw_program_len` (extern statics), and decodes
       them;
    3. builds the image;
    4. runs `run_main_native` (factory: none until S5) on the big-stack
       thread with the Unix terminal, locked standard input and a
       `BufWriter` on standard output;
    5. reports errors as in §2.4, with `stitchwort run`'s exit statuses;
    6. installs mimalloc.
  - A `build.rs` records `--print native-static-libs` into a file next to
    the `.a`, or the lane hard-codes the per-OS list, checked by a test.
  - New `stitchwort build <target> [-o out] [--project]` in
    `crates/cli/src/main.rs`, with the code in a new
    `crates/cli/src/build.rs`. It:
    - checks and lowers exactly as `run` does;
    - encodes;
    - writes `program.o`, containing `sw_program` and `sw_program_len`, with
      the `object` crate (0.40, `write` feature), for the host triple;
    - finds the library (§2.2) and runs `$CC`/`cc` (§2.3);
    - writes `out`, by default the target's name in the current directory.
  - Errors: no `cc` found, no library found, linker failure (with its
    output).
  - The flake's Rust source filter and package include the new crates; the
    package installs `lib/stitchwort/libstitchwort_standalone.a`.
- **Tests** (`crates/cli/tests/build.rs`, using the release or debug `.a`
  that the test build produces; skipped with a message if `cc` is absent):
  - `build` the small IO program, then run it on input; output and exit
    status equal `stitchwort run`'s;
  - `build` a program that fails (`Fail`) and one that runs out of frames;
    the messages and statuses are as specified;
  - `build games/rogue`, then pipe `jjlq`; output equals `stitchwort run
    Rogue.main` on the same input;
  - on macOS, `codesign -v` on the output succeeds;
  - a pseudo-terminal test like `keys_mode.rs`: raw mode restored after `q`
    and after Ctrl-C.
- **Done when:** `stitchwort build games/rogue -o rogue && ./rogue` plays in
  a terminal, which the lane checks itself in a pseudo-terminal, and the
  tests pass. Record the build time and binary size.

**S4. A code generator free of host addresses (after N2a merges).**
- **Files:**
  - `crates/rt/src/native_abi.rs`:
    - `Context.tables: *const Tables`, where
      `#[repr(C)] pub struct Tables { pool, shapes, num_tables, ops, caches,
      n_caches }`;
    - `#[unsafe(no_mangle)]` on every `sw_*` helper.
  - `crates/rt/src/code.rs`: an operations table in `Image` (every distinct
    `PrimOp` used by a `Prim`/`Test`, numbered by `code::compile`), if not
    simpler to keep it in `crates/native`.
  - `crates/native/src/n1.rs`:
    - `Gen::address` uses are replaced: `Const` reads the pool through
      `tables`; `op_address` becomes an index into `ops`; `ApplyCache`s
      become indices into `caches`; `shapes` and `num_tables` come from
      `tables`;
    - code generation is split from the module: `fn emit(module: &mut dyn
      Module, …)`, with `Gen.module: &mut dyn Module`;
    - the JIT path (`compile`) builds `Tables` and keeps every behaviour.
- **Tests:** `crates/native/tests/n1.rs` unchanged and passing (output,
  allocation traces event for event, frame and step limits). Add a test that
  the generated code contains no host address: compile with a recording
  `Module` wrapper, or check that `Gen::address` is gone. And a bench check
  that `task native:bench` is not slower beyond noise.
- **Done when:** the JIT runs only through `Tables`, and the N1 tests pass.
- **As built (26 October 2026):**
  - `native_abi::Tables` is as above. `Numbering::of(image)` numbers the
    operations (distinct `Prim`/`Test` operations, in order of first use)
    and the number tables (each body's, in order), from the image alone, so
    a runtime that rebuilds the image rebuilds the same tables.
    `TableStore` owns the memory and frees it.
  - `sw_prim`, `sw_test` and `sw_num_switch` take the context and a
    number, and read the shapes, the operation or the table themselves.
    Compiled code reads `tables.pool` (for a `Const` of a value in a cell)
    and `tables.caches` (the `Apply` caches, numbered in the order the
    sites are compiled) with `readonly`, movable loads, which Cranelift
    shares and hoists. Traced `Unpack` stores its pairs on the stack.
  - `Gen::address` is gone. `emit(module: &mut dyn Module, …)` makes every
    body, adapter, `apply{n}` stub and trampoline; `compile` wraps it with
    the JIT. Every `sw_*` helper is `#[unsafe(no_mangle)]`.
  - The check: in debug builds, every function's integer constants are
    audited against the host objects the code could name (the image, the
    program, the helpers). `tests/relocatable.rs` checks that
    `n1::listing`, the IR as text, is the same for the same program lowered
    twice at other addresses.

**S5. Object output and `build --native`.**
- **Files:**
  - `crates/native`: add `cranelift-object = "=0.136.2"` (keep the lockstep
    pin), and `pub fn compile_object(program, image, triple) ->
    Result<Object, Vec<String>>`, using `emit` with an `ObjectModule`
    (`is_pic = true`, `preserve_frame_pointers`, `unwind_info` off). It
    exports:
    - `sw_native_manifest`, a read-only data object: the image hash, the
      roots as `(global, trampoline pointer, checks_arguments)`, the cache
      count, and a pointer to `sw_functions`;
    - `sw_functions`, with function relocations;
    - the program data, as in S3.
  - `crates/standalone`: `AotIslands: NativeIslands`, built from
    `sw_native_manifest` (a weak symbol, or always present, with zero roots
    when built without `--native`). It checks the image hash, allocates the
    caches and `Tables`, and runs roots through the same crossing as
    `n1::Islands::call` (move the shared part to `native_abi` so the two
    can't drift).
  - `crates/cli/src/build.rs`: `--native` (requires the `native` feature)
    and `--verbose`, which prints what was compiled and why not, as
    `run --native --verbose` does.
- **Tests:**
  - `build --native` of `micro_call`, `micro_tail` and `set_nat` (small
    sizes): output equals `run`; `--verbose` says each root ran natively;
  - a program over its frame limit gives the same `E-RESOURCE` as `run`;
  - on macOS, `codesign -v`.
- **Done when:** these pass on macOS arm64, and on Linux x86-64 if a Linux
  machine is available to the lane (otherwise note it as unverified).
  Record `micro_call` at 1,000,000: binary against `run --native`.
- **As built (26 October 2026):**
  - **One object.** With `--native`, `stitchwort_native::aot::compile_object`
    runs `n1::plan` and `n1::emit` into an `ObjectModule` (`is_pic`,
    `preserve_frame_pointers`, no unwind information; `n1::host_isa` makes
    the JIT's ISA and this one), and returns the `object::write::Object`.
    The CLI adds `sw_program` and `sw_program_len` to it
    (`build::finish_object`, which also sets the Mach-O platform), so the
    code and the program are one `program.o`. `emit` takes an
    `export_roots` flag: the trampolines are then `sw_root_<global>`,
    exported; the bodies, adapters and `apply{n}` stubs stay local.
  - **The data** (`stitchwort_rt::native_aot`), all read-only with
    relocations, so in `__DATA_CONST` on macOS:
    - `sw_functions`: a pointer per global, its adapter (`value{g}`) or 0;
    - `sw_lambdas`: a pointer per lambda, its body or 0 (absent with no
      lambdas);
    - `sw_roots`: per root, `(global, checks_arguments, trampoline)`, three
      words;
    - `sw_native_manifest` (exported): `magic` ("swnative"), `version`,
      `image_hash`, `n_caches`, `max_frame` (N2b's bound on a frame, for
      the stack check), `n_globals`, `n_lambdas`, `n_roots`, then pointers
      to the three tables: eleven words.

    An object without native code (plain `build`, or `--native` where
    nothing fits) has a manifest with no roots, so the library always finds
    the symbol and needs no weak linking.
  - **The image hash** is FNV-1a over the image's `Debug` text (the codec's
    tests compare images by it; it holds no address). `AotIslands::new`
    checks the magic, version, hash, global and lambda counts and each
    root's global, before any native code runs. On a mismatch the
    standalone `main` prints `internal error: this executable can't run:
    …` and exits with 2, from inside the factory, which `run_main_native`
    calls before the entry is computed, so nothing has run.
  - **The crossing** is `native_abi::Crossing`, which both `n1::Islands`
    and `AotIslands` own: the code's tables (`functions`, `lambdas`,
    `callable`, the `TableStore`), the admission check (`admits`: function
    values in the arguments, and N2b's rule that the frame counter fires
    before the stack check), `call`, and N2b's release of what frames gave
    up on an error. N2b's `floor_depth`, `counter_fires_first`,
    `HOST_ROOM` and `HELPER_ROOM` moved there from `crates/native/src/
    frames.rs` (which re-exports them), so the runtime library needs no
    Cranelift; `Trampoline` moved too.
  - **`--verbose`** prints the plan's notes, then a line like
    ``native: compiled `Main.outer` as native code (2 bodies, in 2.2 ms)``,
    or why the whole run stays on the machine. The binary itself prints no
    notes.
  - **Tests:** `crates/cli/tests/build.rs` (the four benchmarks, each equal
    to `run --native` and `run` and signed; `--verbose`; `Fail`; native out
    of frames; the roguelike), `crates/native/tests/object.rs` (the symbols,
    and no absolute relocation in the text), `crates/standalone/src/aot/
    tests.rs` (a mismatched image, foreign manifest, no roots). The test
    tiers now build the CLI with `--features stitchwort-cli/native`
    (Taskfile `TEST_FEATURES`, and the flake's nextest checks).
  - **Numbers** (Apple M4 Pro, load 33–60, so rough; the note's sizes;
    best of 3):

    | Program | Binary (wall / CPU) | `run --native` (wall / CPU) | Machine-only binary (CPU) | Binary size (stripped) |
    |---|---|---|---|---|
    | `micro_call` 1,000,000 | 0.089 s / 0.074 s | 0.206 s / 0.154 s | 0.832 s | 1,438,080 (1,071,248) |
    | `micro_tail` 20,000,000 | 0.042 s / 0.031 s | 0.138 s / 0.110 s | 0.517 s | 1,438,016 (1,071,232) |
    | `set_nat` 1,000,000 | 3.72 s / 2.58 s | 3.70 s / 4.36 s | 10.72 s | 1,523,448 (1,154,208) |
    | `closures` 1,000,000 | 1.17 s / 0.25 s | 2.38 s / 0.47 s | 0.51 s | 1,473,312 (1,104,608) |

    `run --native` includes checking and compiling (closures: 103 ms of
    Cranelift). A `build --native` took 0.23 s (`micro_*`) to 1.1 s
    (`set_nat`, `closures`, which load more of the library). The roguelike's
    binary is 1,470,272 bytes with `--native`, 8 bytes more than without:
    its one root, `Std.Terminal.toIO`, is blocked only by the effect
    operations (`Bind`, `TailPrim:Effect(Bind)`, `Translate`, `FoldIn`,
    `RunPure`), so nothing compiles until N4.
  - **Linux x86-64: unverified** (no Linux machine in the lane; NO7 of
    native-only.md later ran it, see below).
  - **After N4 (26 October 2026).** S5 was ported to N4's crossing
    (native-compilation.md, "N4 as built"): every body `main` reaches but
    the entry is compiled into the object, the machine linked in runs what
    native code hands it (effects, `Text.fold`, function values without
    code), and the manifest (version 2) lists trampolines by number of
    arguments (`sw_cross_<n>`, `sw_trampolines`) and whether frames nest,
    in place of the roots. `AotIslands` implements `compiled`, `fits` and
    `call` over the shared `Crossing`. `--verbose` says ``native: compiled
    241 of the 242 bodies `main` reaches (frames of at most 2760 bytes, in
    254.6 ms)`` for the roguelike, whose test now checks that (every body
    but the entry) and that its piped output equals `run`'s.

    The seeded roguelike (release build, Apple M4 Pro, load 11–22; a
    500-key piped game, 468,660 bytes of output, identical for both
    binaries and `run`; best of 3):

    | Binary | Wall | Cycles | Instructions | Size (stripped) | Build |
    |---|---|---|---|---|---|
    | `--native` | 0.12 s | 0.50 G | 2.81 G | 2,468,320 (2,080,080) | 1.09 s |
    | machine only | 0.34 s | 1.36 G | 6.90 G | 1,497,800 (1,121,024) | 0.90 s |

    2.7× fewer cycles (0.24 ms a key against 0.68 ms), for about 0.95 MB
    more code.
  - **After NO6 of native-only.md (26 October 2026): no machine inside.**
    A `--native` binary carries the tables and literals native code reads
    (`stitchwort_rt::linked`) instead of the encoded program, and links
    none of the machine, the bytecode compiler or the codec (`nm` checks it
    on the roguelike); the manifest (version 6) names the library's way to
    run the executable, so a machine-only binary also links no native
    runtime. The same seeded roguelike, a 500-key piped game with other
    keys than above (396,274 bytes of output, identical for both binaries
    and `run`; Apple M4 Pro, load 10–25, best of 3), against main before
    NO6 on the same keys:

    | Binary | Wall | Cycles | Instructions | Size (stripped) | Build |
    |---|---|---|---|---|---|
    | `--native` | 0.10 s | 0.40 G | 2.29 G | 2,196,880 (1,847,456) | 1.29 s |
    | `--native`, before NO6 | 0.11 s | 0.43 G | 2.29 G | 2,469,984 (2,080,640) | 1.45 s |
    | machine only | 0.28 s | 1.09 G | 5.56 G | 1,447,152 (1,086,704) | 0.43 s |
    | machine only, before NO6 | 0.27 s | 1.07 G | 5.58 G | 1,531,152 (1,154,480) | 0.46 s |

    0.20 ms a key against 0.56 ms (wall), and the native binary is 233 KB
    (11%) smaller than before; it is 0.76 MB larger than the machine-only
    one. D1287's hybrid is superseded (D1294); NO7 records the rest.
  - **On Linux, after NO7 of native-only.md (26 October 2026).** The S5 and
    NO5–NO6 tests pass on Linux aarch64 (natively, in a NixOS VM) and
    x86-64 (through Rosetta); the platform table in §7.1 has the details.
    Linux needed two fixes: stacks mapped with `MAP_NORESERVE` (glibc's
    thread stacks are accounted memory, and the default overcommit
    heuristic refused `run --native`'s 64 GiB), and the native tables'
    own copy of the shapes (`run --native` had read a stale one). The same
    500-key game on aarch64 Linux: 0.132 s natively against 0.345 s on the
    machine, 1,915,848 bytes stripped against 1,129,384 (macOS, same keys:
    0.124 s and 0.295 s, 1,830,976 and 1,086,736 bytes).

**S6. Every pure primitive through the runtime.**
- **What:** `census::n1_blocker` admits `Prim`/`Test` of `Text`, `Int`,
  `Float`, `TextEqual`, `IntEqual`, `NegSucc` and the `Delay` constructors,
  through `sw_prim`/`sw_test` (§3.1). `Text.fold` and the effect operations
  stay out. `n1.rs` needs only the admission and, if missing, a
  `TailPrim`-free path.
- **Tests:** an `n1.rs` program using text and integer operations agrees
  with the machine, with identical traces; the census snapshot is updated.
- **Done when:** that passes, and the roguelike's census shows only the N3
  and N4 families.

**N3 and N4 (planned already; one addition each).** Their acceptance gains
a `build --native` test of their own fixtures, so that standalone parity is
kept as each lands, not tested at the end. N3's closure instructions must use
`Tables`, as S4 set up, with no host addresses.

**S7. The roguelike fully native. Milestone M2.**
- **What:**
  - `build --native games/rogue`, where `--verbose` must report that every
    body but the entry is compiled (since N4 there are no islands; S5's
    roguelike test checks this already);
  - fix what's left;
  - measure the binary size, build time, and time per turn for a scripted
    500-key game against the machine-only binary;
  - document `stitchwort build` in the guide.
- **Tests:** the piped play-through equals `run`; the pseudo-terminal test
  passes on the native binary; the `Rogue.Tests.PlayThrough` script, run
  through the binary, equals its expected frames.
- **Done when:** `stitchwort build --native games/rogue -o rogue && ./rogue`
  plays with every reachable body compiled.

**Sizes:** 7 lanes beyond N2–N4. M1 needs S1–S3, which can start now in
parallel with N2a (S1 and S2 at once, then S3).

## Decisions

All three are **decided by Claude, provisional** (Matt asked for the
work to go on tonight). They stand unless Matt overturns them.

**D1287. Is the hybrid the architecture, or a stopgap?** **Decided by
Claude, provisional: the architecture.**
- Overturned by Matt (D1294, 26 Oct): binaries are fully native; see native-only.md.
- **What it means:** a standalone binary always links the machine. It runs
  whole native islands where they fit, and the rest on the machine, by the
  same rule as `run --native`.
- **What `build --native` does when something doesn't fit:** it doesn't
  refuse. It builds, and `--verbose` says what wasn't compiled and why. A
  `--require-native` flag can come if someone needs a guarantee.
- **Why:**
  - It gives a playing roguelike before N3 and N4 (M1).
  - The machine costs about 150 KB.
  - It keeps one execution model for `run` and `build`.
- **The alternative:** require the whole program to compile, with no
  machine in the binary. That delays any standalone binary until after N4,
  and removing the machine still needs the entry glue compiled (§3.2).

**D1288. What does the binary carry: the lowered program, or the source
with a checker?** **Decided by Claude, provisional: the lowered,
erased program, encoded by a new codec.**
- **Why:**
  - Its binaries are well under 1 MB plus the program, against more than
    18 MB.
  - Start-up is milliseconds, against seconds of checking.
  - No proofs or kernel are in the binary (§5).
- **The cost:** a codec to keep in step with the IR. It is versioned and
  refuses mismatches, and the binary and the CLI come from one build.

**D1289. How is the binary linked?** **Decided by Claude, provisional: the
system `cc`, against a prebuilt runtime static library installed beside the
CLI. No cargo, and no bundled linker.**
- **What users need:** a C toolchain at `build` time (Xcode's command line
  tools on macOS), and nothing at run time.
- **Why:**
  - Linking takes 0.16 s.
  - On macOS it signs for us.
  - Every Cranelift AOT toolchain found does the same (§8.2).
- **The alternatives:**
  - cargo needs a Rust toolchain and takes tens of seconds.
  - A bundled lld is a large C++ dependency, and then we'd own signing.

  Either can be revisited if users without a C toolchain matter.

## Appendix A: the experiment

**[ran]** In this worktree, reverted after the run. The patch is in the
session's scratch directory as `aot/standalone-experiment.patch`, and the
library crate as `aot/swrt/`.

1. **Code changes:**
   - `#[unsafe(no_mangle)]` on the 18 `sw_*` helpers in `native_abi.rs`;
   - `Helpers::declare` and `Gen.module` take `&mut dyn Module` instead of
     `&mut JITModule` (it compiled with no other change);
   - `cranelift-object = "=0.136.2"`;
   - a copy of `n1::compile` building an `ObjectModule` (`opt_level =
     speed`, `preserve_frame_pointers`, `is_pic` on or off), exporting each
     root's trampoline as `sw_root_<global>`, and an example binary that
     checks, lowers and compiles a file to `.o`.
2. **The input:** `micro_call.sw` with `outer 1000000 0`. Compiling its two
   bodies and the trampoline took 2.1 ms, and the object was 3,160 bytes
   (Mach-O arm64).
3. **The library:** a scratch crate depending on `stitchwort-rt` and
   mimalloc, as a `staticlib`. Its C `main` builds a `Context` (no limits on
   steps, frame limit 2,000,000, no stack check, no function table, no run),
   calls `sw_root_8(ctx, [Nat 1000000, Nat 0], out)` as the machine's
   crossing would, and prints the result.

   This skips the program, the machine and the host. The embedded host
   addresses (§1.4) were wrong in the binary, but `micro_call` never reaches
   the slow paths that use them.
4. **Link:** `cc micro_pic.o libswrt.a -Wl,-dead_strip` took 0.16 s. With
   both the Nix clang wrapper and `/usr/bin/cc`, the linker was ld64-956.6.
5. **Results:**

   | Run | Result | Time (wall) |
   |---|---|---|
   | standalone binary (PIC) | `Nat(20000000)`, 22,000,000 steps | 0.13–0.18 s |
   | standalone binary (non-PIC) | `SIGBUS`, after linker alignment warnings | — |
   | `stitchwort run --native` (includes checking) | `20000000` | 0.32–0.37 s |
   | `stitchwort run` (the machine) | `20000000` | 2.25 s (1.06 s user; load 44) |

   | Binary | Size |
   |---|---|
   | linked, dead-stripped | 813 KB |
   | stripped | 586 KB |
   | stripped, with `run_main_on` (the machine and runner) also linked | 735 KB |
   | the `.a` (LTO) | 6.7–7.0 MB |

6. **Signing:**
   - The linked binary was `adhoc,linker-signed`.
   - After `strip -o` it was still `Signature=adhoc`, and it ran.
   - With the signature removed, it exited 137.

## S6 as built (26 October 2026)

**[ran]** Nothing was left to admit. N3 had admitted every `Prim` and `Test`
except the effect operations and `Text.fold`, the `Int` instructions and
`Text.chars`. `stitchwort dev opcode-census` on `Rogue.main`, `Aoc.Day01` to
`Aoc.Day09` (project `aoc/`) and `bench/native/*.sw` lists no blocker but
`Prim:Effect` and `TailPrim:Effect` (the only `TailPrim`s the lowering emits
are effect ones), so the census is unchanged: rogue 170 of 244 bodies
(standard library 43 of 54), AoC days 1 to 9: 45/56, 41/59, 43/56, 49/52,
47/67, 65/68, 60/68, 84/97, 92/105. `Text.fold` occurs in none of them (it
stays out, as the plan says). What S6 added is the test
(`crates/native/tests/s6.rs`: `Nat` division and remainder with words, big
numbers and the divisor 0 of `Nat.divFuel`; `Int` of every sign and size;
`Float` with `NaN` and infinities; `Text` with empty and multi-byte text;
`Delay` constructors; each agrees with the machine, event for event in the
allocation trace; division under every step and frame limit), and the two
cheap wins of N3's profile:

- **`Nat.divFuel` inline** (`/` and `%` compile to it): when the fuel, the
  dividend and the divisor are words, `fuel` if the divisor is 0, else
  `min(fuel, n / d)` in a `udiv`; anything else goes to `sw_prim`.
- **A partial application given exactly the rest of its arguments**, headed
  by a compiled global function or a closure, is set up by
  `sw_apply_prepare` straight into the plan (no `Vec`s: the new arguments
  moved up, the held ones cloned in front, the function value dropped last),
  with the machine's order of clones and drops.

**Measured** (Apple M4 Pro, release, best of 3 by cycles, 1,000,000 elements
/ keys, `run --native`; load average well below N3's): `closures` 1.48 G
cycles, 5.13 G instructions on main, 1.27 G and 3.82 G after (-14% cycles,
-26% instructions); `Set` inserts 11.26 G cycles, 45.19 G instructions on
main, 11.22 G and 44.85 G after (the `Set` keys use `%` only in their
generation).
