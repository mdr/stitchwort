# Evaluation of the Stitchwort Rust implementation

Code review, 1 November 2026. Baseline: `2308bc9ac977ae6d21d5eff93c970553667510b6`.

**Overall assessment:** this is a thoughtfully engineered research compiler with strong testing practices and a sensible broad architecture. The Rust is generally direct and idiomatic. Its main weakness is that important invariants are spread across large mutable structures and APIs whose correctness depends on callers following comments. That is manageable during rapid development, but becomes increasingly expensive as features, execution modes and long-lived editor sessions accumulate.

I would keep the architecture and improve its boundaries. I would also fix the concrete issues below before doing cosmetic cleanup. In particular, the native backend deserves a focused unsafe-Rust review: it contains both careful ownership engineering and places where Rust's usual safety guarantees have been bypassed without a sufficiently restrictive API.

This is a review of implementation quality, not a proof of the kernel's soundness or an exhaustive security audit. It combines broad inspection of the workspace, deeper reading of selected subsystems, normal checks, and small independent probes. No implementation changes were made.

## 1. Findings to act on first

| Finding | Practical consequence | Evidence | Priority |
|---|---|---|---|
| Native layout probe reads padding as an initialized integer | Undefined behavior in a safety check used before native execution | Source inspection; the same read pattern is rejected by Rust's constant evaluator | Fix promptly |
| Compiler/test fingerprint omits the fast runtime's source | A rebuilt runtime can reuse results produced by older runtime code | Actual build-script probe; traced through the fast test-cache lookup | Fix promptly |
| Native compilation exposes borrowed raw pointers through an owning-looking safe API | Safe Rust callers can construct an executor whose tables refer to a dropped image | A compile-only probe using the actual public APIs succeeds | Fix the unsafe boundary promptly |
| Background proof actions have no document-version guard or bounded worker pool | Suggestions can refer to old text; repeated requests can start overlapping expensive searches | Source inspection; a live race probe timed out rather than returning a result | Improve editor reliability |
| Kernel environment can be mutated outside kernel admission | The trusted boundary relies on front-end discipline as well as kernel checking | A safe-Rust probe changes a final declaration's type and then admits a false theorem | High architectural priority; not a source-language exploit |

“Fix promptly” does not mean I observed a user-visible crash or a false Stitchwort theorem accepted from a normal source file. Each finding's exact scope is explained below.

### 1.1 The native layout probe reads uninitialized padding

In [native_abi.rs](../../crates/rt/src/native_abi.rs), `probe_functions` reads the first eight bytes of a `Fun` as a `u64` at lines 294 and 315, then masks away the bytes between its tag and its index.

The relevant representation has a one-byte tag at offset 0 and a four-byte index at offset 4. Bytes 1–3 are padding: Rust does not promise they are initialized. Reading the entire word as an integer is invalid even if the next operation masks those bits out. The safety comment establishes address validity and size, but misses initialization. [Rust's initialization rules](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html#initialization-invariant), [requirements of pointer reads](https://doc.rust-lang.org/std/ptr/fn.read.html#safety).

I checked a minimal reproduction with this repository's Rust 1.99.0 compiler:

```rust
#[repr(u8)]
enum Fun {
    Global(u32),
    Closure { lambda: u32, captures: [usize; 2] },
}

const KEY: u64 = {
    let f = Fun::Global(0x0abc_def0);
    let first = unsafe { (&raw const f).cast::<u64>().read() };
    first & 0xffff_ffff_0000_00ff
};
```

Rust reports `E0080`: the read requires initialized memory, but bytes `0x1..0x4` are uninitialized. This reproduces the invalid read pattern, not a crash in the complete native backend. Ordinary tests can pass because hardware often returns some bits for the padding; that does not make the Rust operation valid.

**Recommendation:** read the initialized tag and index separately, as their actual types, and combine them. The nearby `words` helper already follows the more careful field-by-field approach. Audit similar layout reads and add an interpreter-based check for the Rust side of the ABI. The existing small Miri-oriented tests in [prims.rs](../../crates/rt/src/prims.rs) are a useful precedent; running the JIT itself inside Miri is a different problem.

### 1.2 The test fingerprint does not cover the runtime that runs the tests

[driver/build.rs](../../crates/driver/build.rs) hashes sources under `syntax`, `core`, `elab` and `driver`, plus the lockfile, compiler identity and target. It does not include `crates/rt/src`.

But [driver.rs](../../crates/driver/src/driver.rs) now runs fast tests through `stitchwort_rt::Machine`. Its cache key includes that driver fingerprint, the test's content hash and execution-mode flags. A cache hit returns before the test runs. The `m` mode marker distinguishes the fast runner from the reference runner; it does not distinguish versions of the fast runner.

I copied the fingerprint inputs to a scratch directory and invoked the actual compiled build script. After editing a runtime source file, both fingerprints were unchanged. A driver-source edit was the positive control and changed both:

| Change | Compiler fingerprint changed | Source fingerprint changed |
|---|---|---|
| Edit `rt/src/prims.rs` | No | No |
| Edit `driver/src/fingerprint.rs` | Yes | Yes |

The consequence follows directly from the cache lookup: changing the runtime while keeping the Stitchwort test and the other inputs unchanged can reuse an old pass or failure. This can hide a runtime regression during development. It is not evidence that the logical kernel accepts an invalid proof.

The separate [runtime build hash](../../crates/rt/build.rs), used for encoded-program compatibility, is useful but is not incorporated into this test-cache key. The source fingerprint is also advertised as a way to detect a stale WebAssembly bundle, so its scope deserves the same review.

**Recommendation:** define the dependency set for each fingerprint explicitly, include the runtime where its behavior affects the result, and test the collection of inputs—not just the hashing function. Include manifests/features and code generators where they can affect behavior. A separate checker fingerprint and runner fingerprint could avoid invalidating kernel-check caches unnecessarily.

### 1.3 Native code lifetimes are documented but not enforced

[n1::compile](../../crates/native/src/n1.rs) accepts `&Program` and `&Image` and returns an `Islands` value with no lifetime parameter. Its tables contain pointers into the image's constants and number tables. [TableStore](../../crates/rt/src/native_abi.rs) explicitly documents that these must outlive the store, but stores raw pointers without retaining the owner or expressing the borrow.

The normal `NativeExecutor::new` path compensates with a `WithImage` owner that retains the image and drops the code first. That is good engineering. The public safe APIs nevertheless allow a different construction path:

```rust
fn dangling_executor(program: &Program)
    -> Result<NativeExecutor, Vec<String>>
{
    let image = stitchwort_rt::code::compile(program);
    let outline = stitchwort_rt::linked::Outline::of(program, &image);
    let code = stitchwort_native::n1::compile(
        program, &image, Default::default()
    )?;
    Ok(NativeExecutor::from_outline(
        outline, Box::new(code), Limits::default(), 8 * 1024 * 1024
    ))
    // image is dropped, while code's tables still point into it
}
```

I compiled this against the actual workspace libraries; it needs no `unsafe` at the call site and compiles successfully. I did not execute the dangling code. A program whose compiled code accesses the discarded pool or number tables would access freed storage.

The same family of APIs also lets a caller supply code, an image and an outline separately, with their agreement enforced by convention. The current CLI follows the intended construction path, so this finding is about the Rust API's safety boundary rather than an observed CLI use-after-free. In Rust, an abstraction containing unsafe operations must remain safe for its safe callers; a comment requiring a caller to preserve a hidden raw-pointer lifetime is insufficient. [Rust's definition of a sound unsafe abstraction](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).

**Recommendation:** make a compiled artifact own the data its pointers reference, or carry the required lifetime. Bundle the compatible image/code/outline rather than accept unrelated pieces. Where an unsafe promise genuinely cannot be expressed through ownership, keep the constructor narrow and mark that boundary explicitly unsafe. Do not spread unsafe requirements across otherwise ordinary runner APIs.

### 1.4 Editor proof actions need versioning and bounded scheduling

The main editor-checking path in [lsp.rs](../../crates/cli/src/lsp.rs) has a sensible single checker, cancellation flag and document versions. The proof-action path at `code_action` is separate: every request starts a detached thread, captures the current text and goal range, performs a search and sends its response directly.

[actions_for](../../crates/cli/src/lsp.rs) emits an unversioned `WorkspaceEdit.changes` edit. It does not tie the edit to the document version from which it was computed. An edit made while the search is running can move or replace the hole; the result still contains the old range. The protocol supports versioned document edits so clients can check the version before applying them, subject to client capabilities. [LSP TextDocumentEdit](https://raw.githubusercontent.com/microsoft/language-server-protocol/gh-pages/_specifications/lsp/3.17/types/textDocumentEdit.md), [WorkspaceEdit capabilities](https://raw.githubusercontent.com/microsoft/language-server-protocol/gh-pages/_specifications/lsp/3.17/types/workspaceEdit.md).

There is also no worker cap or request-specific cancellation in this path. The five-second search setting is not a substitute for bounding concurrency or all preprocessing work. Multiple requests can retain project snapshots and independent checking sessions simultaneously.

I attempted a live probe that requested an action, immediately changed the document and waited for a response. It timed out after 35 seconds on this busy machine; it did not demonstrate an applied stale edit. The missing version guard and unbounded thread creation are verified directly in the source. Existing action tests cover successful results, but do not establish behavior during this race.

**Recommendation:** use a bounded search worker/queue, cancel superseded requests, and associate results with the source version. Return versioned edits when supported and suppress stale results otherwise. Add tests for a document changing during search, cancellation and repeated requests. Keep this separate from the already useful cancellation of ordinary checking.

### 1.5 Kernel admission is not a fully encapsulated Rust boundary

The kernel rechecks submitted terms, and important fields such as declaration bodies and admission states have restricted visibility. However, [Globals](../../crates/core/src/globals.rs) publicly exposes its definition and datatype vectors. Several logical fields of a final definition, including `ty` and `ty_value`, are publicly mutable through them. Test-only admission bypass methods are also compiled as public methods rather than isolated behind a testing feature.

A small probe using only safe Rust can:

1. Declare an empty proposition and a correctly checked natural-number definition.
2. Directly replace the definition's stored type and evaluated type with the empty proposition.
3. Ask the kernel to admit a theorem of that proposition by referring to the altered definition.

The final admission succeeds. This demonstrates that mutating the trusted environment can invalidate what kernel checking establishes. It is not a Stitchwort source-language soundness counterexample: the probe deliberately breaks the environment through the Rust API.

The architectural implication matters. “The kernel checks what the elaborator produces” does not by itself mean every elaborator bug is contained. That guarantee also depends on every caller respecting the mutability rules of already admitted declarations and other shared state.

**Recommendation:** make logical state of final declarations read-only outside the kernel. Expose views and narrow metadata setters where needed. Separate pending declaration construction from final declaration access, and isolate test bypasses. This can be incremental; it does not require redesigning the type theory.

## 2. What the codebase does well

### 2.1 The major subsystems have sensible boundaries

The architecture is recognizable and useful:

| Layer | Responsibility | Assessment |
|---|---|---|
| `syntax` | Lexer, surface syntax, parser, spans and diagnostics | A reusable front end; also supports formatter and documentation tools |
| `core` | Explicit terms, evaluation, conversion, kernel checking and termination | Independent checking code exists; shared environment needs stronger encapsulation |
| `elab` | Resolve names, infer omitted information, desugar and generate core definitions | Correct place for most surface-language complexity; now the largest maintenance burden |
| `driver` | Sessions, projects, checking orchestration, search, caches and diagnostics | Valuable common layer for CLI and browser |
| `rt` | Erasure/lowering, runtime IR, bytecode, execution and native ABI support | Clear separation from logical proof acceptance, but now broader than its original name suggests |
| `js`, `native`, `standalone` | Output generation and executable integration | Distinct execution targets without forcing Cranelift into the browser |
| `host`, `cli`, `web` | Operating-system facilities and user interfaces | Host-specific code is mostly kept away from the language logic |
| `fmt` | Formatting with validation | Particularly good example of a narrow, defensive component |

A one-page diagram of the crates, their dependencies and sizes, regenerated from the workspace, is in [docs/architecture/crates.pdf](../architecture/crates.pdf).

This is not a codebase that needs a new framework or a wholesale rewrite. The dependency direction is broadly appropriate, and the shared driver avoids independently reimplementing the compiler in each user interface. Native compilation is optional for the CLI and absent from the WebAssembly playground's dependency graph.

There are imperfections: the core crate also contains printing, elaborator metavariables and a partial-program runner; the runtime crate contains much of the compiler's backend support. Crate names therefore should not be read as exact maps of the trusted computing base. These are manageable organizational issues, not proof that the broad split is wrong.

### 2.2 The testing strategy checks relationships between implementations

The strongest aspect is the use of comparisons that are likely to expose mistakes:

- A simple recursive evaluator is retained separately from the main evaluator, with explicit independence rules in [reference.rs](../../crates/core/src/reference.rs).
- Runtime and native tests compare behavior across execution paths, including effects, resource counts and cleanup on error exits.
- [check_cache.rs](../../crates/driver/tests/check_cache.rs) compares fresh and cached sessions using a canonical dump, diagnostics and navigation.
- [rewind.rs](../../crates/driver/tests/rewind.rs) compares rewound/cancelled sessions with a fresh check.
- Kernel tests construct malformed terms directly, bypassing the elaborator; [kernel fuzzing](../../crates/core/tests/fuzz.rs) extends this beyond hand-selected examples.
- [Soundness fuzzing](../../crates/driver/tests/soundness_fuzz.rs) mutates statements and proofs and searches accepted mutants for counterexamples.
- The formatter reparses its output and checks that it represents the same program before returning it. See [fmt/lib.rs](../../crates/fmt/src/lib.rs).

These are substantially better assurances than a large collection of snapshots alone. Snapshots remain valuable for diagnostics, generated JS and public outputs, but are supported by behavioral checks.

The limits also matter: implementations share some primitives and representations, so they can share a bug. The canonical state dump is itself maintained by hand. Fuzzing can find counterexamples but cannot establish soundness. The native-padding finding demonstrates why ordinary success tests need complementary unsafe-code checking.

One test-design weakness surfaced in this review: [the search JSON snapshot](../../crates/cli/tests/search.rs) compares output that depends on how far a wall-clock-limited search gets. The merge run reached its ten-second limit before the expected rewrite checks, changing the counts, warnings and rewrite list. The test already normalizes some variable counters, but not all time-dependent output. Prefer a deterministic work/candidate budget for exact-output tests, and test deadline handling separately. Updating the snapshot to whichever partial result a loaded machine produced would preserve the fragility.

### 2.3 Resource exhaustion has an explicit meaning

[budget.rs](../../crates/core/src/budget.rs) treats running out of work, stack, frames, size or being cancelled as a separate outcome. It explicitly avoids turning “could not finish checking” into “proved false” or “the test failed.” Nested attempts have documented semantics, including propagation of a stack exhaustion to the surrounding operation.

That is a serious and appropriate design for a compiler which evaluates programs during type checking. Cancellation support and tests that compare debug/release behavior show attention to operational details that are easy to neglect.

The design also acknowledges its engineering tradeoffs: some passes recurse on a large Rust stack, while the evaluators use explicit work stacks. Large reserved stacks are address space, not automatically that much resident memory. The [host stack wrapper](../../crates/host/src/stack.rs) documents its operating-system assumptions and cleanup obligations.

### 2.4 Safe Rust is the default

The workspace denies `unsafe_code`, with local exceptions rather than an unrestricted default. Most of the language implementation uses enums, pattern matching, owned vectors, `Result`, and reference-counted immutable structure.

`Rc` shares a value without cloning its entire tree. `RefCell` permits checked-at-runtime mutation in a single-threaded object graph. Both are reasonable tools for a compiler session. Their presence is not evidence of poor Rust, and replacing them indiscriminately with arenas, `Arc`, or pervasive lifetime parameters would not automatically improve the design.

The low-level style is generally readable. There are few unnecessary abstraction hierarchies; compiler-specific concepts are usually represented explicitly. Newtypes such as `DefId`, `DataId`, `GlobalId` and `LambdaId` prevent some accidental index mixing.

The limitation is that `Rc` and `RefCell` do not enforce the compiler's higher-level invariants. A borrow can be memory-safe while a final theorem's stored type has been changed incorrectly. That is where narrower APIs would help most.

### 2.5 Comments explain invariants and failure modes

Modules such as [termination.rs](../../crates/core/src/termination.rs), [undo.rs](../../crates/elab/src/undo.rs), [queue.rs](../../crates/elab/src/queue.rs), [native_abi.rs](../../crates/rt/src/native_abi.rs) and [host/stack.rs](../../crates/host/src/stack.rs) explain why their algorithms are valid and which assumptions they rely on. This is valuable documentation, especially in AI-authored code where a later contributor may otherwise preserve the shape while breaking the reason it works.

Comments are not infallible: the padding read's safety explanation is incomplete. Nevertheless, writing down the invariant makes that omission discoverable. Retain this practice while reducing historical ticket narration where it obscures the current contract.

## 3. Where the architecture needs improvement

### 3.1 Reduce the number of places that must know all compiler state

The elaborator is roughly 89,000 source lines. Its main object holds name resolution, inference, effects, postponed checks, generated helpers, proof goals, diagnostics, navigation and other tables. Many fields are independently mutable through `RefCell` or `Cell`.

This is convenient for implementing features. It also means that adding one piece of state may require changes to several mechanisms:

- Speculative elaboration rollback.
- Declaration cleanup and clearing inference state.
- Session marks and rewind after editing.
- Cache encoding and replay.
- Canonical dumps used to test those operations.

[undo.rs](../../crates/elab/src/undo.rs) carefully records and restores these relationships. That is a strength and a warning about the maintenance cost. A newly added table can be omitted from both the operation and the dump used to test it, allowing the comparison to miss the omission.

**Recommended direction:** group state by ownership and lifetime. For example, separate per-attempt inference state, per-declaration generation state, persistent checked metadata and presentation state. Give each group responsibility for its own checkpoint/restore and serialization where appropriate. Keep the top-level transaction responsible for composing those checkpoints.

Do this incrementally when touching those areas. A generic transaction framework that merely hides the same manual list would not solve the problem. Neither would splitting a 5,000-line file into ten files while all ten still mutate the same unrestricted object.

### 3.2 Make phase transitions explicit

Several representations are publicly constructible, and correctness depends on a caller pairing the right pieces: core declaration versus checked declaration, lowered program versus validated lowered program, program versus compiled image, and native code versus its backing tables.

[Program::validate](../../crates/rt/src/validate.rs) is a useful check. [The runtime decoder](../../crates/rt/src/codec.rs) bounds counts and nesting and validates decoded programs. The missing step is to make selected entry points accept the validated/owned result rather than any raw collection of fields.

For a non-Rust reader, the principle is simple: make it difficult to hand the next stage an object that only looks finished. Rust's private fields and distinct wrapper types can enforce this without a large class hierarchy.

**Recommended direction:** a few carefully chosen types such as a read-only checked declaration view and an owned prepared native artifact. Avoid a wrapper for every helper function; apply the technique where crossing a boundary changes what may safely be assumed. The native-lifetime finding is the clearest immediate use case.

### 3.3 Keep the logical trust boundary explicit

The default cache replay deliberately skips kernel rechecking. [cache/mod.rs](../../crates/elab/src/cache/mod.rs) documents this and the decision behind it. Checksums, build fingerprints, dependency hashes and a directory salt help detect corruption or inappropriate reuse; they are not a replacement for checking an arbitrary hostile proof object.

That is a legitimate performance choice for a local cache under a defined threat model. It changes the promise: a warm `check` trusts a previous compiler run and its local cache, while `--no-cache` performs the full checking path. This should be explicit in architecture documentation and in claims about independent checking.

I would keep three concerns distinct:

1. Logical checking of newly submitted core declarations.
2. Trusted replay of locally produced checked state.
3. Runtime correctness of extracted/native programs and their input boundaries.

A bug in the fast runtime cannot normally construct a logical proof for the kernel, but can produce a wrong program answer or wrong test evidence. A compromised cache is a different trust problem. A public mutable kernel environment is a third. Calling all three “the kernel” makes review less precise.

**Recommendation:** maintain a short current map of the trusted components and bypass paths. Isolate trusted replay behind a deliberately named interface. Preserve cache-free checks and direct malformed-core tests as independent validation paths.

### 3.4 Consolidate backend contracts without eliminating independent oracles

The shared runtime code already avoids some divergence between JS, bytecode and native compilation. Erasure rules, native binding recognition, specialization and the runtime IR provide useful common machinery.

The JS generator is still about 6,300 lines in its main file, with boundary classification, codecs, source generation and TypeScript-facing decisions interleaved. The runtime and standalone codecs also carry build-format contracts. Native compilation adds ABI layout and ownership contracts of its own.

**Recommendation:** separate backend-neutral representation/erasure contracts from target-specific emission and boundary codecs. In JS, splitting boundary planning from generated runtime code and `.d.ts` emission would improve review locality. Review the fingerprint dependency graph at the same time: the stale-cache issue is a concrete example of a shared contract drifting behind the implementation.

Do not merge the reference evaluator into the optimized implementation just to reduce duplication. Its different control flow is the point. Share stable definitions where appropriate, but keep independent behavior oracles capable of disagreeing.

### 3.5 Use a small structured internal error classification

The user-facing diagnostics have stable codes and helpful source context. Internally, some decisions depend on string codes: for example, [undo::fatal](../../crates/elab/src/undo.rs) identifies a non-recoverable resource failure using `e.code == "E-RESOURCE"`. Other elaboration paths inspect codes to decide whether to retry or postpone work.

This is understandable and not a demonstrated misclassification. As error framing and deferred checks grow, however, a presentation code is a fragile way to represent control flow.

**Recommendation:** add a compact internal classification for recoverable mismatch, blocked inference, resource exhaustion and cancellation, while retaining the existing public diagnostic codes. The type system can then help ensure a resource failure does not accidentally turn into a failed speculative candidate after an error is reworded.

This is a targeted improvement, not a request to introduce an error-handling framework throughout the workspace.

## 4. Low-level Rust assessment

### 4.1 Ownership is mostly appropriate, but manual restoration needs care

The code uses scope guards effectively for budgets, erasure and transparency. A scope guard is a value whose destructor restores a temporary setting when a scope exits, including during ordinary error propagation.

Some other temporary settings use manual save/change/call/restore sequences, for example gluing modes in [elab/kernel.rs](../../crates/elab/src/kernel.rs). These restore correctly when the inner function returns an error; they do not restore if it panics. That is acceptable if the entire session is discarded after a panic. It becomes dangerous if a long-lived host catches the panic and reuses the session.

**Recommendation:** use guards for short-lived mode changes where practical, and state a clear policy that panicked compiler sessions are discarded. Do not promise general panic recovery merely because Rust allows unwinding. The worker test helper already drops its worker state after a caught panic, which is the right instinct.

### 4.2 Panics are not uniformly a problem

An `expect("tests are checked before they run")` at an internal compiler invariant is different from an `unwrap` on user input. I would not replace every assertion with a generic error and thereby hide compiler bugs.

The review should instead ask whether an invariant is established at the boundary that needs it. The bounded readers, parser errors and structured resource errors are good examples. Public runtime/native APIs accepting malformed or mismatched structures need stronger contracts, as discussed above.

At C/JIT boundaries, unwinding deserves particular attention. Native ABI helpers contain assertions whose failure may abort rather than unwind through compiled frames. Document that policy and test abnormal exits through those paths. Error cleanup tests are already substantial, but they are not the same as testing every Rust panic route.

### 4.3 The native ABI has an unusually large maintenance obligation

Native code reads the runtime value representation and reference-counted allocation layout directly. Some of that representation is fixed with `repr(u8)`; some relies on the pinned Rust standard library implementation. The project includes layout probes, explicit frame bounds, allocation tracing and detailed ownership notes to compensate.

That is a conscious engineering choice, not automatically bad Rust. It is also the area where “small change” can have a disproportionate effect: a new enum variant, changed payload, compiler upgrade or missing owner can invalidate a low-level assumption. The two native findings show that this is active maintenance work rather than a theoretical concern.

Prefer supported ownership operations and explicit ABI records when their cost is acceptable. Where direct layout access is retained, keep a single documented contract, minimize the unsafe surface and review its safety comments against actual Rust validity rules. Rust's public `Rc` API provides raw-pointer and reference-count operations; its private internal fields are not themselves an application ABI. [Rc documentation](https://doc.rust-lang.org/std/rc/struct.Rc.html).

The macOS JIT provider also keeps thread-local write-protection state in an object declared `Send`. Its module comment requires compilation/finalization to stay on one thread. That requirement deserves an explicit review of movement and failure paths, because moving allocation addresses safely is not the same as transferring a thread-local permission setting. I have not reproduced a failure here; this is a focused follow-up for the unsafe review, not an additional confirmed bug.

### 4.4 Large files matter because of mixed responsibilities

At the reviewed revision, examples include:

| File | Lines | Useful decomposition |
|---|---:|---|
| `syntax/parser.rs` | 7,699 | Expression parsing, patterns, layout and recovery, with a common parser cursor |
| `js/lib.rs` | 6,280 | Boundary planning, codec generation, JS emission and TypeScript emission |
| `elab/check.rs` | 5,990 | Application elaboration, expected-type propagation and special expression forms |
| `elab/lib.rs` | 4,862 | State definitions, module setup, admission orchestration and library embedding |
| `core/value.rs` | 3,790 | Evaluation, conversion and quotation, with carefully explicit shared contracts |
| `core/check.rs` | 3,461 | Term checking, declaration admission and datatype checks |

Line counts include comments and inline tests; they are navigation signals, not a defect metric. Some long `match` statements are clearest when kept together. Start with mixed responsibilities and unstable boundaries, rather than impose an arbitrary maximum file size.

Avoid changing many unrelated algorithms while moving code. A mechanical extraction with unchanged behavior is easier to review than a cleanup that simultaneously changes evaluation and borrowing structure.

### 4.5 Avoid speculative performance rewrites

Cloning an `Rc` is not the same as copying a tree; copying a context vector may be significant or negligible depending on the workload. The code has timing instrumentation and deterministic work/allocation benchmarks, so performance changes can be justified with evidence.

I would not recommend blanket arena conversion, replacing all `String`s, universal interning, removing `RefCell`, adding `unsafe` to hot loops, or aggressively genericizing the evaluator based on inspection alone. Improve ownership boundaries first, then profile specific expensive operations.

The deterministic hasher is an explicit choice for reproducible allocation counts. Its comment says it does not resist chosen collisions and assumes a compiler reading its own user's code. That is reasonable for the current local workflow. A public compilation service would need a different threat-model review rather than silently inheriting the same assumption. This is not an immediate requested change.

## 5. Validation and limits

The workspace inventory found 14 crates, 200 Rust files under `src` and approximately 182,000 lines there, including inline tests and comments. Another 160 Rust files sit outside `src`, predominantly integration tests and their helpers. The review sampled all major layers; it did not inspect every line or every unsafe helper.

Checks performed:

- `cargo fmt --all --check`: passed.
- `cargo clippy --release --workspace --all-targets -- --deny warnings`: passed.
- `nix develop -c task test:merge`: **1,038 passed, 1 failed, 149 skipped**, in 215.336 seconds. The failure was `stitchwort-cli::search::what_closes_a_goal`, whose snapshot differed after the ten-second search deadline; it was not an incorrect proof being accepted. The machine was running other work concurrently, so this run is not a clean benchmark of the tier's intended duration.
- An isolated rerun of `what_closes_a_goal` passed in 3.651 seconds. The concurrent standard-library documentation changes caused a rebuild before that rerun; no Rust implementation file relevant to the findings changed. This supports the timing-dependence diagnosis, but does not turn the original merge run into a passing run.
- Padding read: Rust 1.99.0 rejects the minimal constant-evaluation reproduction with `E0080`.
- Fingerprint inputs: the actual compiled build script was insensitive to the runtime-source edit and sensitive to the driver-source control edit.
- Native lifetime: the safe-call construction of an executor retaining pointers into a dropped local image compiled successfully; it was not executed.
- Kernel encapsulation: the deliberately corrupted Rust environment admitted the false theorem; ordinary Stitchwort source cannot perform that mutation.
- LSP race: source-level finding; the live request timed out after 35 seconds and the probe process was terminated.

Probe files and logs are in `/tmp/stitchwort-rust-review-probes/`; check logs are `/tmp/stitchwort-rust-review-{fmt,clippy,merge}.log`. These are scratch evidence, not repository implementation changes. The probes left no running language server. ReText and its two helper processes were stopped and checked to be absent.

The checkout received concurrent commits while this review ran. The main Rust files supporting the findings remained unchanged from the baseline during inspection; concurrent changes included standard-library documentation and documentation-related tests. Results from this machine are not a substitute for Linux, browser and architecture-specific gates. Miri and sanitizers were not run; the installed environment did not provide `rustup` or a Miri toolchain, and the padding issue was checked with Rust's constant evaluator instead.

The repository has substantial local test automation in [Taskfile.yml](../../Taskfile.yml), [nextest profiles](../../.config/nextest.toml) and Nix. The checked-in GitHub Actions workflow is a manually invoked playground deployment, rather than an automatic Rust test gate. If automatic remote regression checking is wanted, wire a bounded existing tier into CI instead of inventing a second test policy. This is an organizational improvement, not evidence that local checks are not being run.

## 6. Recommended sequence

1. **Correct the padding reads and fingerprint inputs.** Small changes with focused regression checks. The normal test suite is useful but will not by itself detect either class.
2. **Tighten the native ownership API.** Make compiled code retain, or borrow explicitly, its backing storage. Review unsafe constructors, safe trait contracts and program/image agreement together.
3. **Make final logical declarations read-only outside the kernel.** Preserve convenient metadata access while routing logical changes through admission. Remove production availability of test-only bypasses.
4. **Bound and version background editor work.** Extend the existing checking model to proof-action searches instead of creating unrestricted parallel sessions.
5. **Group state as features are touched.** Reduce the maintenance list shared by rollback, rewind, cache replay and canonical dumps. Retain differential state tests throughout.
6. **Improve review locality.** Split mixed backend/parser/elaborator responsibilities in small mechanical changes, and keep the architecture/trust map current.

The codebase has enough good structure and testing to support these improvements incrementally. The important shift is to make more of its existing invariants enforceable by Rust, so a future contributor needs to remember fewer unwritten relationships when adding a feature.
