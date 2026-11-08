# A small-object allocator for cells?

SW-2360, 8 November 2026. Paper lane: code and sources read, nothing built
or run. Status: proposed, D3413 and D3414 open.

**In short.** We shouldn't write an allocator of our own. mimalloc stays
the allocator, as it is for Lean and Koka. Lean has dropped its own small
allocator: the premise in lean-runtime-speed.md §1.3 is out of date (§2
below). What's worth doing is cutting the work around each allocation and
free. Native code would keep a short list of freed cells in its run
`Context` and pop or push them inline, with mimalloc behind it for
everything else. On binary-trees I estimate that removes 25–35% of the run
time. That's inferred from the profile in §1, not measured. The cell's own
header (dropping `Rc`'s weak count, an 8-byte header) belongs to the
compact-values design (SW-2324, D3358), not to an allocator.

## 1. Where the time goes

**The problem, plainly.** binary-trees builds and throws away about 68
million tree nodes. Each node costs us about 23 ns to build, check and
free. About 10 ns of that is spent handing the memory to and from the
allocator. Native code itself is doing little in that time.

SW-2321's profile after its change (binary-trees at depth 18, 1,640
samples, 1.60 s; `profile-after.txt` in the SW-2321 session's scratchpad)
**[measured]**:

| Where | Self time |
|---|---|
| generated code (`Tree.check`, `Tree.make`) | 55.9% |
| `mi_free` | 14.4% |
| `mi_malloc_aligned` | 11.4% |
| other mimalloc (page queue, `madvise`, free-list extend, bitmaps) | ~5% |
| Rust wrappers: `cell_new` 5.6, `sw_cell_free` 4.0, `sw_cell_new` 1.7, `Rc::drop_slow` 1.3, alloc shim 1.3 | 13.9% |

The call counts are 68.3 M `sw_cell_new` and 67.8 M `sw_cell_free`, so
nearly every node is built and freed by native code. Allocator plus
wrappers is about 45% of samples, or about 10.5 ns per node. mimalloc
itself takes about 6 ns of that: 2.7 ns per allocation and 3.4 ns per
free. That's mimalloc running its fast path, not mimalloc going wrong.

On matcher (5,579 samples) the allocator is 21.6% (`mi_free` 7.4,
`mi_malloc_aligned` 6.8). The allocations are spread more widely: 35 M
cells (20 M freed inline by `sw_cell_free`, the rest by Rust drops through
34.9 M `sw_drop_words`), 20 M closures at two allocations each, and binds
**[measured counts]**.

## 2. What other runtimes do

| Runtime | Allocation | Freeing | Source |
|---|---|---|---|
| **Lean 4** (master, 7 Nov 2026; release 4.34) | mimalloc v3. `lean_alloc_small_object` calls `lean_alloc_small_object_core`, which reads mimalloc's thread heap ("theap") from Lean's own thread-local and calls `mi_theap_malloc_small`. mimalloc is compiled into the same C file (`#include <static.c>`), so its fast path is inlined: one call per object | `mi_free` directly | `src/include/lean/lean.h:510-600`, `src/runtime/mimalloc.cpp:1-55` **[read]**; PRs leanprover/lean4#7786 (mimalloc 3) and #14950 (one translation unit) **[web]** |
| Lean 4.13 (2024) | `LEAN_SMALL_ALLOCATOR`: Lean's own size-class allocator, `lean_alloc_small(sz, slot)` | its own | `~matt/.elan/.../v4.13.0/include/lean/lean.h:323-335` **[read]**; the 4.34 header has no `LEAN_SMALL_ALLOCATOR` **[read]** |
| **Koka** (Perceus) | mimalloc v3. `kk_malloc_small` is `mi_theap_wmalloc_small(ctx->heap, …)`, with the theap taken from the context passed to every function, not from thread-local storage. Perceus reuse turns many free-and-allocate pairs into in-place updates | `mi_free_small_nonnull`, or `mi_free` | `kklib/include/kklib.h:510-550` **[read]** |
| **OCaml** | Bump allocation in the minor heap, inline: lower `young_ptr`, compare with `young_limit`. In OCaml 5, each domain has its own minor heap | none: a copying minor GC and a major GC | from memory |
| **GHC** | Bump allocation in the nursery through the `Hp`/`HpLim` registers, checked once per block of code | none: a generational copying GC | from memory |
| **Swift** | `swift_allocObject` calls `swift_slowAlloc`, which is `malloc` (the system allocator) | `free`. The optimiser moves non-escaping objects onto the stack | from memory |

**What this shows.**

- The two reference-counted runtimes closest to ours both use mimalloc,
  and Lean went from its own allocator to mimalloc. mimalloc was designed
  for exactly these runtimes (Leijen, Zorn and de Moura, "mimalloc: Free
  List Sharding in Action", 2019; from memory).
- What they changed is the path to it. Each takes one call into mimalloc's
  small-object entry, with the heap pointer already in hand, and no
  alignment or size-class arithmetic. Koka keeps that pointer in the
  context passed to every function, which is what our `Context` is.
- What saves the most is not allocating at all: Perceus and Lean's reuse,
  our `CtorReuse` (SW-2359 is widening it).
- The tracing-GC runtimes are fast at this for a reason that doesn't carry
  over: a bump pointer works because nothing is freed one by one.

lean-runtime-speed.md §1.3 says the difference is "the call path and
staging, not the allocator". That still holds, but its "small-object
allocator" describes Lean before mimalloc 3.

## 3. Constraints here

- **Rust frees cells anywhere.** A cell is `Fields(Rc<[Value]>)`
  (`crates/rt/src/value.rs:60`). Any drop in the runtime, the machine or a
  helper frees it through `Rc`, and so through `#[global_allocator]`
  (`Fields::drop`, `value.rs:364`). On stable Rust 1.99
  (`rust-toolchain.toml`), `Rc` can't take a custom allocator, because
  `allocator_api` is unstable. So memory that native code hands out as a
  cell must be memory Rust can free through the global allocator, or
  cells must stop being `Rc`.
- **The global allocator differs between binaries.** The CLI
  (`crates/cli/src/main.rs:534`), the standalone executable
  (`crates/standalone/src/lib.rs:43`) and most test binaries use mimalloc.
  The counting allocators in `crates/rt/tests/effect_alloc.rs:48` and
  `state_match.rs:39` wrap the system allocator, and `crates/bench/src/lib.rs:34`
  wraps mimalloc. The playground (`crates/web`) has no
  `#[global_allocator]`, so wasm32 uses Rust's default, dlmalloc. Native
  code calling `mi_*` directly would break any binary whose Rust allocator
  isn't mimalloc. This is what SW-2321 meant by keeping the allocator on
  the Rust side.
- **The allocation trace.** It identifies cells by address, renumbered by
  first appearance (`crates/rt/src/alloc_trace.rs:16-18`). When code is
  compiled with `trace_refcounts`, native code takes the helper paths
  (`crates/native/src/n1.rs:82`, `:114`), so a cache can be compiled out of
  traced code. This is already how the inline unique paths of `Unpack`
  work.
- **Native code and the machine share values.** A cell built by one can be
  freed by the other. So recycled memory has to be a normal `Rc` allocation
  of the same layout once it's handed out.
- **Threads.** `Value` holds `Rc`, so it isn't `Send`. A run's values stay
  on its thread. Every native function gets the run's `Context` as its
  first argument (`native_abi.rs:467-509`). Parallel runs (`test`, the LSP)
  each have their own `Context`. A cache in `Context` needs no
  synchronisation and no thread-local storage.
- **Unaffected.** The JS backend (JS objects and its GC), and the
  playground, which runs the machine but not native code.

## 4. Options

Each gain is for binary-trees unless it says otherwise, estimated from the
per-node figures in §1.

**A. Tune mimalloc and call it more directly.** Replace
`mimalloc::MiMalloc` with our own `GlobalAlloc`. Its `alloc` would call
`mi_malloc` when the alignment is at most 16, which mimalloc always
guarantees. `MiMalloc` calls `mi_malloc_aligned` every time
(`mimalloc-0.1.52/src/lib.rs:50-61`), and that function checks the
alignment and then tries an aligned fast path
(`v3/src/alloc-aligned.c:185-240`). Raise `purge_delay`, whose default is
1,000 ms (`v3/src/options.c:140`), so freed pages aren't returned to the
OS between phases (`madvise` is 1.3%).

- Gain: 2–5% (part of `mi_malloc_aligned`'s 11.4%, plus the ~2% spent
  purging and re-extending pages). Low confidence.
- Risk: very low. It applies everywhere the CLI allocates, including
  checking.
- Cost: about 30 min.

**B. Per-size free lists in front of mimalloc, behind
`#[global_allocator]`.** A wrapper keeps thread-local lists for the cell
sizes.

- Gain: small. mimalloc already is thread-local per-size free lists. The
  wrapper saves only its page lookup and thread-id check, and adds a
  thread-local access, which on macOS is a call through a TLV descriptor.
  mimalloc avoids that with a reserved slot: `tpidrro_el0`,
  `v3/include/mimalloc/prim.h:182`.
- Risk: medium. It covers every allocation in the compiler. Lists are
  stranded when an elaborator thread ends. Allocating inside a TLS
  destructor makes it reentrant.
- Cost: 60–90 min.
- Not recommended.

**C. A per-run cell cache in `Context`, popped and pushed inline by native
code** (recommended).

- **How it works.**
  - `Context` gets a list head for each fixed size, 1 to 8 fields
    (`FIXED_CELL`, `native_abi.rs:1436`).
  - `new_cell` (`n1.rs:3554`) pops the head: load it, branch if it's null,
    load the next pointer, store the new head, then store counts 1/1 and the
    fields. It calls `sw_cell_new` only when the list is empty.
  - `Unpack`'s emptied-cell path (`n1.rs:4363`) pushes the cell instead of
    calling `sw_cell_free`, unless the list is at its cap.
  - The end of the run drains the lists through the existing
    `sw_cell_free` path. Every cached block is an `Rc<[Value]>` allocation of
    exactly its arity that was never deallocated, so draining frees it with
    the same layout.
  - A handed-out block is a normal `Rc` again, and any Rust drop frees it
    through the global allocator. This is the same reasoning as in-place
    reuse (an allocation kept and refilled), and `probe_layout` already pins
    the offsets.
  - It works under any global allocator, and needs no thread-local storage.
  - Traced code doesn't use it.
- **Gain.**
  - binary-trees: 25–35% (about 1.60 s down to 1.05–1.2 s). The inline pop
    and push are about 7 instructions per node, against about 10.5 ns of
    allocator and wrapper time now. Some of the mimalloc samples are cache
    misses on the block itself, and those will move into generated code,
    hence the range.
  - matcher: 3–6%. Only the 20 M cells native code frees itself are
    covered; Rust-dropped cells and closures aren't.
  - All inferred.
- **Risk.**
  - Memory. The cache holds freed cells that mimalloc could have given to
    other sizes, so it has a cap: a byte budget per run, past which frees go
    to mimalloc. Peak memory is measured before and after.
  - Unsafe code. The path is untraced, so it gets its own checks: a count of
    cached blocks that must drain to zero, and the differential outputs.
- **Cost.** About 60–90 min (Opus: layout and unsafe code).

**D. Lean's way: native code calls mimalloc's small-object entry
directly.** Native code calls `mi_theap_malloc_small` with the theap cached
in `Context`, and `mi_free`.

- Gain: 12–18%. It removes the wrappers (13.9%) and part of
  `mi_malloc_aligned`. `mi_free`'s 14.4% stays: in v3 it looks up the page
  map, checked on Apple (`v3/include/mimalloc/internal.h:668-674`), and
  compares thread ids (`v3/src/free.c:179-205`).
- Risk: every binary that runs native code must have mimalloc as Rust's
  allocator, or Rust frees mimalloc blocks with another allocator. The
  counting test allocators break that, and Rust can't check it at run time.
  Inlining mimalloc's fast path, as Lean does, would need a C shim
  compiled together with mimalloc's source.
- Cost: medium.
- Gains less than C, and assumes more.

**E. A heap and cell header of our own; cells stop being `Rc`.**

- What it is: a custom `Cell` pointer type with an 8-byte header (a 32-bit
  count, the tag, the arity). It has no weak count, so a two-field cell
  shrinks from 64 to 56 bytes even before compact fields. It does its own
  freeing in `Drop`.
- That's what compact values needs anyway (SW-2324, D3358). Once we own
  the header, the allocator behind it is a free choice, and per §2 the
  choice should still be mimalloc, called as Lean and Koka call it. Then
  the cache in C becomes this type's free path, for Rust drops too.
- Gain: it's compact values' gain (1.3–2× on allocation-heavy code,
  lean-runtime-speed.md §3.5), not an allocator's.
- Cost: the largest; it is SW-2324.

## 5. Recommendation

Do C, after A as a cheap first measurement. Leave the header and `Rc` to
SW-2324 (E), with mimalloc behind it.

Why C over D: C gains more because it skips `mi_free` as well as the
wrappers, and it makes no assumption about which allocator a binary has.
C is also what Koka does in spirit (the heap state comes from the context,
not from thread-local storage), with an exact-size list in front.

What it rules out: nothing. The cache is about 100 lines in `Context`, the
helpers and `n1.rs`. SW-2324 can absorb it or delete it.

## 6. Questions for Matt

- **D3413: End state: mimalloc stays the allocator behind cells and
  closures; Stitchwort doesn't write a general small-object allocator of its
  own.** Native code gets an exact-size cell cache in its run context in
  front of mimalloc. [rec: yes. Lean and Koka both use mimalloc's fast path
  (Lean moved to it from its own allocator), and the profile shows mimalloc
  at its fast path, so what's left to remove is the work around the calls.]
- **D3414: Scope: the cell's header (dropping `Rc` for an 8-byte header
  with no weak count) is designed in SW-2324 (compact values), not as an
  allocator change.** [rec: yes. It changes the same layouts native code,
  the machine and `probe_layout` share, so doing it twice would mean two
  migrations of the same unsafe code.]

**Calls I made** (implementation, reversible):

- The cache sits in `Context`, not in thread-local storage.
- It's keyed by arity 1 to 8, as the fixed helpers are.
- It has a per-run byte cap (start at 64 MB, tune by measurement) rather
  than no cap.
- Traced code skips it.
- Stage A goes first because it's cheap and gives a cleaner baseline.

## 7. Tickets to file

Each stage profiles before and after with `task profile:native --
binary-trees matcher` (and octopus), records samples and the allocator
share, and times `bench/compare` binary-trees, matcher and octopus on an
idle machine. A stage that doesn't move its target profile is reverted.

1. **Stage A: mimalloc called directly, and purge delay (Sonnet, 30–45
   min).**
   - Change: a `GlobalAlloc` in `stitchwort-host` or a small shared crate,
     used by the CLI, the standalone executable and `test-alloc`, that calls
     `mi_malloc` or `mi_free` when the alignment is at most 16. Try
     `purge_delay` at start-up in the standalone executable.
   - Tests: `task test:one` on `probe_layout` and the `crates/native` n1
     cell tests.
   - Keep it only if binary-trees moves 2% or more.
2. **Stage B: the per-run cell cache (Opus, 60–90 min).** Option C.
   - Tests: the n1 cell tests (`crates/native/tests/it/n1.rs`), a new test
     that a run's cache drains to zero, traced runs still equal to the
     machine's, and the compare outputs.
   - Measure: as above, plus peak RSS on binary-trees (`/usr/bin/time -l`)
     against the cap.
   - Follows SW-2359, since both edit `CtorReuse` and `new_cell`'s
     neighbourhood.
3. **Stage C: Rust-side frees into the cache (Sonnet, 60 min). Gated:**
   only if stage B's matcher profile still shows cells freed through
   `sw_drop_words` as 5% or more.
   - Change: `Fields` holds a `ManuallyDrop<Rc<[Value]>>`, and on its last
     reference it pushes to the active run's cache (reached through
     `Context`, or a thread-local pointer set at native entry).
   - Tests: `rt`'s value and drop tests, plus the n1 tests.
4. **Stage D: a closure in one allocation (Opus, 60–90 min). Gated on
   matcher's profile.**
   - Change: `Fun::Closure`'s captures stored inline after the `Fun`, not
     in a separate `Box` (two allocations today, `value.rs:90`; 20 M closures
     on matcher). Then closures can use the cache.
   - It overlaps SW-593 and SW-2324 (both rewrite `Fun`), so check with them
     first.
5. **No allocator stage after these.** The header and the end of `Rc` go to
   SW-2324 (D3414).

**Findings worth filing:**

- `Fields::drop` and `free` (`value.rs:364-372`, `:303`) gather children in
  a fresh `Vec`. Dropping a unique cell with a heap child allocates and
  frees that `Vec`: one more mimalloc round trip per top-level drop.
  Lean threads its deletion list through the freed objects' own headers
  (`lean.h:163-169`). A small inline stack, or a reused buffer, would
  remove it. On matcher, `free`, `Fields::drop`, `take_children` and the
  drop glue are about 10% self **[measured]**. The `Vec`'s own share wasn't
  separated. Sonnet, 30 min.
- lean-runtime-speed.md §1.3 describes Lean as having its own small-object
  allocator. Since mimalloc 3, Lean calls mimalloc's small-object entry
  directly (§2). That's a one-line correction to the research note.
- The playground runs the machine on wasm's default dlmalloc. Its
  allocator share is unmeasured; profile it before choosing anything for
  wasm.

**Not checked:**

- OCaml, GHC and Swift are from memory.
- I didn't check whether nixpkgs' Lean 4.34.1, the comparison's Lean, is
  built with `USE_MIMALLOC`. It's on by default (`CMakeLists.txt:107`).
- All gains are inferred from one profile. None is measured.
- I didn't look at octopus's profile.
