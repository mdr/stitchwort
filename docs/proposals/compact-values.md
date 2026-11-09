# Compact values: how big a run-time value should be, and how to find out before rebuilding it

SW-2324, 8 Nov 2026, Opus, paper lane (nothing built or run). It answers D3358 (compact
values as the runtime's end state, a note first) and D3431 (Matt, 8 Nov 2026: "Do a
literature review, comparative language analysis of similar implementations, and
understand how this might fit into the Stitchwort world. Also, have it suggest how we might
verify that this bet pays off for us ... plan how we might measure. We don't want to commit
to a large refactoring that doesn't pay off."). It takes the cell header from
[cell-allocator.md](cell-allocator.md) (D3414), and builds on
[docs/research/lean-runtime-speed.md](../research/lean-runtime-speed.md) §1.2 and §3.5
(SW-2318), [SW-2296](../reviews/SW-2296-native-profiles.md),
[SW-2363](../reviews/SW-2363-cell-cache.md), [SW-2417](../reviews/SW-2417-native-effect-share.md)
and [SW-2295](../reviews/SW-2295-comparative-speed.md) (the latest Overmind run, at
`e11c7b3c2`).

Labels: **[read]** seen in the code, with the place; **[measured]** from one of the reports
above, cited; **[derived]** arithmetic on measured numbers, shown; **[estimated]** a guess
at an effect, with the reasoning; **[cited]** from a paper or a project's sources, named;
**[memory]** from memory of a project or paper, not rechecked for this note.

## 0. Summary

- **The problem.** A run-time value is three machine words (24 bytes), and a constructor's
  cell has a 16-byte header plus 24 bytes per field. A list cell or tree node is 64 bytes;
  Lean's is 24. A `Map` node is 136 bytes; Lean's is 48 **[read]**.
- **The finding that changes the bet.** On the latest comparison run, native code executes
  11.3 times as many instructions as Lean (geometric mean), and is 11.7 times slower
  **[derived, §1.4]**. So almost all of the gap is *work done*, not *waiting for memory*:
  native code retires instructions at about the same rate as Lean does. Smaller values pay
  only through the instructions they remove (fewer words moved, stored, spilled and saved)
  plus a small part of the cache stalls. Shrinking memory alone, which is what compact cells
  with three-word registers (option B in lean-runtime-speed.md) would do, can recover at
  most the instruction-rate gap: about 1.04× on the geometric mean, 1.3× on binary-trees.
- **The options** (§3): (C) our own 8-byte cell header, no weak count; (E) **two-word
  values**, which nobody had proposed: only `Data` and `Text` use the third word, for a
  length, so moving the length into the object makes every value 16 bytes with no new
  encoding of numbers or floats; (A) one-word tagged values, as in Lean, Koka and OCaml;
  (D) unboxed scalar fields chosen per type, which (A) needs for `Float`; (B) compact cells
  behind three-word registers, which the measurements argue against.
- **The recommendation** (§6). End state: **C, then E; A with D only if the measurements
  say so.** Before any of it, about 5–6 lane-hours of measurement (§5): a census of what
  values a run makes, hardware counters on Overmind, an instruction-by-instruction count of
  the work that exists because values are three words, and a "dilation" experiment that
  makes cells *bigger* without adding instructions, to measure what their size costs. Each
  step has a go/no-go stated in advance. My estimate before measuring: C gives 1.01–1.03×
  on the geometric mean against Lean, C+E 1.05–1.12×, A+D another 1.05–1.10× on top, with
  binary-trees the largest single gain (C+E about 1.15–1.3×) **[estimated]**.
- **V4's result** (§7, from the measurements). C about 1.01× (lower than estimated above);
  C+E 1.09× on the decision set's geometric mean and 1.21× on binary-trees (range
  1.03–1.21× and 1.09–1.46×); A another 1.08×. Each is just under its gate (1.10×, 1.25×,
  1.10×), so the recommendation there is to hold E, do four cheap changes first, and rerun
  the model after operations in place stage D **[estimated from measured inputs]**.
- **Work.** Measurement 5–6.5 lane-hours; C 4–6 h; E 10–16 h; A+D 25–40 h more.

## 1. The problem, measured

### 1.1 What a value and a cell are today

All **[read]** in `crates/rt/src/value.rs` and `crates/rt/src/native_abi.rs`.

- `Value` is a `repr(u8)` Rust enum of 24 bytes (`value.rs:27-54`; `a_value_is_three_words`,
  `value.rs:397`):
  - word 0: the kind byte (`TAG_*`, `native_abi.rs:73-84`) and, for `Tag` and `Data`, the
    constructor's tag in bytes 4–7;
  - word 1: the payload: a `u64` `Nat`, `i64` `Int`, `f64` `Float`, or an `Rc`'s address;
  - word 2: a length, used **only** by `Data` (the cell's field count, the fat pointer of
    `Rc<[Value]>`) and `Text` (`Rc<str>`'s byte length). Every other kind leaves it 0
    (`words`, `native_abi.rs:122-150`).
- Numbers and floats are never boxed: `Nat` under 2^64, `Int` in `i64` and every `Float`
  sit in word 1. A constructor without fields is `Tag(t)`, no allocation. The constructor's
  tag is in the value, so a `match` reads no memory.
- A cell is `Rc<[Value]>`: a strong count, a weak count, then the fields at 24 bytes each
  (`STRONG_AT`, `WEAK_AT`, `RC_VALUE_AT`, `native_abi.rs:106-108`).
  - Nothing in the runtime makes a `Weak` (grep of `crates/rt/src`), yet every uniqueness
    test loads and compares both counts (`unique`, `crates/native/src/n1.rs:4629-4635`;
    `machine.rs:1509`; `value.rs:366`).
- A closure is two allocations: `Rc<Fun>` and a `Box<[Value]>` of captures
  (`value.rs:89-91`). `Fun`'s largest variant, `Pap { head: Value, args: Box<[Value]> }`,
  makes `Fun` about 48 bytes, so an `Rc<Fun>` is about 64 before its captures
  **[inferred from the layout; the census in §5 checks it with `size_of`]**.
- An `Array` is `Rc<Vec<Value>>`: the `Rc` holds the `Vec`'s pointer, capacity and length,
  and the elements are a second allocation, 24 bytes each (`ARRAY_ITEMS_AT`,
  `native_abi.rs:112-113`). Reading an element is two dependent loads before the element.
- Native code holds each bytecode register as three Cranelift variables and passes each
  argument as three words (`n1.rs` header, "Registers" and "Frames"). The machine holds a
  `Vec<Value>` of registers (`machine.rs:104`).

Sizes of common cells (Lean's from `lean.h`, §2):

| Cell | Stitchwort today | Lean 4 |
|---|---:|---:|
| `[x, ..rest]`, `Node l r`, `Position { row, column }` | 16 + 2 × 24 = 64 B | 8 + 2 × 8 = 24 B |
| `Some x` | 40 B | 16 B |
| `Map.Tree.Bin size left key value right` (`std/Map/Raw.sw:22`) | 16 + 5 × 24 = 136 B | 48 B |
| an `Array` of 30 M numbers (memory-game) | 720 MB + 40 B | 240 MB + 24 B |
| a closure capturing 2 values | ~64 + 48 B, two allocations | 24 + 16 B, one |

### 1.2 Where size shows up in the profiles

- **binary-trees' peak memory is the cell size.** Peak footprint 69.2 MB **[measured,
  SW-2363]**. The stretch tree of depth 19 has 2^20 − 1 nodes; at 64 bytes that is 67 MB
  **[derived]**. At Lean's 24 bytes it would be 25 MB.
- **binary-trees: 9% of the whole program is prologue and epilogue** in `Tree.check`
  (six pairs of callee-saved registers, a 272-byte frame), which SW-2296 attributes to
  three-word values **[measured share; the attribution is SW-2296's reading of the code]**.
  Another 5% is per-call bookkeeping, which is SW-2322's, not this note's.
- **Copying fields.** Before the fixed-size helpers, `memmove` in `sw_ctor` was 7.2% of
  binary-trees **[measured, SW-2296]**: three words per field.
- **Allocation and freeing.** 20–38% of self time across the ten programs, and recursive
  freeing (`sw_drop_words` → drop glue → `mi_free`) 15–26% of every AoC program
  **[measured, SW-2296]**; 51–53% of expressions and scan **[measured, SW-2417]**. Most of
  that is the *number* of allocations (closures, cells, binds), which compact values does
  not change. It changes their *size*, and the per-field work of the walk that frees them
  (`take_from` looks at each field, `value.rs:271-277`).
- **The cell cache's lesson** (SW-2363): removing 30% of binary-trees' instructions (all of
  mimalloc's fast path) saved only 10% of its time **[measured]**, because what remained,
  the generated code's chains of dependent loads and stores, set the pace. A function's
  share of a profile overstates what removing it saves. Every estimate below is discounted
  for this.

### 1.3 Per program

| Program | What it allocates or holds | Where size might cost |
|---|---|---|
| binary-trees | 68 M two-field nodes, built and freed | footprint (64 vs 24 B), field stores, prologue saves |
| matcher | 35 M cells, 20 M closures, a tree `Map` | list cells, closures (two allocations), 136-B `Map` nodes |
| dijkstra | tree `Map` as queue and table, `Position` records | 136-B `Map` nodes, record cells |
| octopus | lists and `Position` records from `around` | list cells, records |
| memory-game | one 30 M-element `Array`, one `Game` record per turn | 720 MB array (3× Lean's): page faults and TLB, not per-access misses (a random access touches one line either way) |
| expressions, scan | parser closures, binds, effect nodes | count of allocations dominates; size second |
| pidigits | big numbers | none: the time is `num-bigint` |

### 1.4 Instructions against time: most of the gap is work, not waiting

From SW-2295's latest run (Overmind, i7-6700HQ, `e11c7b3c2`; Lean's instruction counts
from the 13:28 run, unchanged since) **[measured counts; ratios derived]**:

| Program | time native/Lean | instructions native/Lean | native G instr/s | Lean G instr/s | Lean rate / native rate |
|---|---:|---:|---:|---:|---:|
| pidigits | 0.65 | 0.71 | 7.15 | 6.54 | 0.91 |
| binary-trees | 2.85 | 2.20 | 7.51 | 9.72 | **1.29** |
| memory-game | 5.92 | 15.76 | 7.69 | 2.89 | 0.38 |
| dijkstra | 13.09 | 13.06 | 7.34 | 7.35 | 1.00 |
| octopus | 14.70 | 11.71 | 8.98 | 11.28 | 1.26 |
| disk | 18.77 | 17.67 | 7.93 | 8.42 | 1.06 |
| expressions | 75.45 | 56.60 | 6.92 | 9.23 | 1.33 |
| scan | 77.35 | 55.21 | 7.31 | 10.24 | 1.40 |
| matcher | 10.30 | 9.23 | 8.47 | 9.46 | 1.12 |
| bridge | 19.38 | 16.94 | 7.41 | 8.47 | 1.14 |
| **geometric mean** | **11.65** | **11.25** | | | **1.04** |

What it says:
- The geometric-mean gap is 11.65×, of which 11.25× is instruction count. Only a factor of
  1.04 is native code running its instructions more slowly than Lean runs its own.
- Smaller values help in two ways: fewer instructions, and fewer cache misses. The second
  can at most close the last column: 1.04× on the mean, 1.29× on binary-trees, 1.3–1.4× on
  the parsers. Even that is an upper bound, because the rate also depends on branches,
  calls and dependent chains, not only on memory.
- memory-game shows the reverse: Lean is waiting for memory there (2.9 G instructions per
  second, a random walk over a 240 MB array), and native code does 16 times the work while
  waiting for the same misses.
- Caveat: instructions per second isn't instructions per cycle, and a program with many
  cheap instructions can hide stalls behind them. Step V1 (§5) measures cycles and stalls
  directly.

**So the question for the refactor is: how many instructions exist because a value is
three words?** That's what §5's step V2 counts. Per node of binary-trees, native code runs
about 315 instructions and Lean 143 (21.64 G and 9.82 G over about 68.7 M nodes)
**[derived]**. A two-field node's three-word handling is plausibly 20–50 of those 172 extra
(field stores, loads, counts, saves) **[estimated]**.

## 2. Other implementations

### 2.1 The comparison

| Runtime | Value word | Object header | Small numbers | Floats | Unboxed fields | How polymorphic code sees values | What it costs |
|---|---|---|---|---|---|---|---|
| **Stitchwort today** | 24 B, self-describing | 16 B (`Rc`: strong + weak) | inline in word 1, 64-bit | inline, never boxed | none: each field a 24-B value | uniformly, with kind and constructor tag in the value | 2.7× Lean's cell size; three registers per value |
| **Lean 4** | 8 B pointer or scalar | 8 B: `m_rc` (i32), `m_cs_sz` (16 bits), `m_other` (8: number of pointer fields), `m_tag` (8) **[cited: lean.h]** | `n << 1 \| 1`, low bit 1 **[cited]**; fieldless constructors too | boxed (`lean_box_float` allocates) where the type is polymorphic; raw in scalar fields and typed code **[read, SW-2318; memory]** | `UInt8`–`UInt64`, `Float`, `USize` stored raw after the pointer fields (`lean_ctor_set_uint32` at a byte offset; "the runtime does not track the size of the scalar area") **[cited]** | type-directed boxing in the IR (`explicitBoxing`), `_boxed` wrappers for closure calls **[read, SW-2318]** | needs types in the IR; Float boxed in lists |
| **Koka** (Perceus) | 8 B `kk_box_t` | 8 B, with refcount (32 bits), scan size, tag **[memory]** | low bit 1, 63-bit **[cited: kklib `box.h`]** | inline when the 11-bit exponent fits 10 bits, else heap **[cited: `box.h`, `KK_BOX_DOUBLE64`]** | value types (structs) unboxed in fields and registers, boxed in polymorphic positions **[memory]** | boxed uniform word | boxing at polymorphic boundaries; mimalloc behind |
| **OCaml** | 8 B | 8 B (size, colour, tag), GC **[memory]** | low bit 1, 63-bit | boxed, except all-float records and float arrays stored flat **[memory]** | OxCaml (Jane Street, 2024–25): "mixed blocks" with `float#`, `int32#`, `int64#` fields stored flat, at the price of generic operations such as polymorphic compare **[cited: OCaml workshop 2024]**; layouts as kinds **[cited: ML workshop 2023]** | uniform word | 63-bit ints; float boxing outside the special cases |
| **GHC** | 8 B pointer | 1 word (info pointer) + payload | boxed (`I#`) unless strictness analysis unboxes; `-funbox-small-strict-fields` by default **[memory]** | boxed (`D#`), same | `{-# UNPACK #-}`, unboxed tuples and sums, levity polymorphism **[memory]** | uniform pointer; **pointer tagging**: the low 3 bits carry the constructor (or "evaluated"), worth 14% on average **[cited: Marlow, Yakushev, Peyton Jones, ICFP 2007]** | laziness; boxing unless optimised |
| **Swift** | no uniform word: a value is its type's size | 16 B for class objects (isa + refcount) **[memory]** | raw | raw | everything is unboxed by type | through value witness tables; an existential is a 3-word inline buffer plus metadata and witness tables, larger values going to the heap **[memory]** | unspecialised generic code is slow; specialisation fixes it |
| **Rust** | none: monomorphised | none | raw | raw | all | monomorphised; niche layout (`Option<&T>` is 8 B) | code size. Our `Value` is 24 B because `Rc<[Value]>` and `Rc<str>` are fat pointers |
| **MLton** | whole-program choice per datatype | 1 word, GC | untagged where types allow **[memory]** | unboxed where monomorphic | flattened by whole-program analysis | no polymorphism left after monomorphisation | whole-program compile |
| **Roc** | monomorphised, unboxed by type | refcount before the allocation **[memory]** | raw | raw | all; recursive tag unions use pointer tag bits **[memory]** | monomorphised; Morphic is for in-place mutation, not layout | compile-time specialisation |
| **Idris 2** (Chez) | Chez's tagged word | Chez's | 61-bit fixnums **[memory]** | flonums boxed, unboxed locally since Chez 10 **[memory]** | none | uniform | GC'd Scheme objects |
| **Agda** (MAlonzo) | GHC's | GHC's | GHC's | GHC's | GHC's | through GHC | as GHC |
| **V8** | 4 B compressed pointer or 31-bit Smi | map pointer | Smi | heap numbers, unboxed in some fields | — | uniform | pointer compression cut the heap about 40% with small speed gains **[cited: v8.dev, 2020]** |
| **HotSpot JVM** | 4 B compressed oop | 12–16 B; compact headers make it 8 B | — | raw fields | all primitives raw | typed | compact headers: about 22% less heap and 8% less CPU on SPECjbb2015 **[cited: JEP 450/519, JDK-8354672]**; 2002's one-word headers gave −1.5% to +2.2% speed **[cited: Bacon, Fink, Grove, ECOOP 2002, as summarised]** |

### 2.2 What the evidence says about payoffs

- **Headers alone are worth single-digit percent.** JVM header shrinking (JEP 450: 8% CPU
  on SPECjbb; Bacon et al. 2002: about ±2%) is the closest measured analogue of option C.
  Those are GC'd systems, where a smaller heap also means fewer collections; we have no
  collector, so our share should be lower.
- **Pointer tagging was worth 14% in GHC**, but most of that was laziness (not entering an
  already evaluated closure). Our values already carry the constructor tag *outside* the
  cell, which is the benefit pointer tagging buys. A one-word design (A) gives that up
  unless it tags pointers too (§3.4).
- **One-word values with tagged scalars** are what every fast reference-counted functional
  runtime uses (Lean, Koka; OCaml with a GC). None of them published an ablation against
  wider values, because none ever had wide values. C13 in
  [compilation.md](../research/compilation.md) measured 5× between our values and unboxed
  numbers on a hand-written Rust `Set` insert, an optimistic bound with ideal code
  **[measured there]**.
- **Floats are the price of one word.** Every one-word runtime boxes floats somewhere and
  then spends effort unboxing them again: OCaml's float records and arrays, OxCaml's mixed
  blocks, Lean's scalar fields, Koka's inline encoding of most doubles, Chez's local
  unboxing. Today we never box a float.
- **Recent work on reference counting** (Perceus, PLDI 2021; frame-limited reuse, ICFP
  2022; FP², Lorenzen, Leijen and Swierstra, ICFP 2023; Ullrich and de Moura, "Counting
  Immutable Beans", IFL 2019) is about *not allocating* (reuse, borrowing), not about value
  width. Lean's move from its own allocator to mimalloc 3 (cell-allocator.md §2) is the
  other recent change. Lean's `@[unbox]` attribute is registered in its IR, but as of 2024
  its developers said unboxing structures through it wasn't implemented (single-field
  structures are unboxed anyway) **[cited: Lean Zulip, Feb 2024]**; I couldn't confirm its
  state in 2026.
- **The structural lesson:** the fastest designs either know types at run time
  (monomorphising: Rust, Swift specialised, MLton, Roc) or keep a one-word uniform value and
  unbox selectively by type (Lean, Koka, OCaml). Our IR erases types before the runtime IR
  (lean-runtime-speed.md §4), but the lowerer still knows each constructor's declared field
  types. That's enough for option D.

## 3. Options for Stitchwort

Each is an end state. Untouched in every option: the kernel, the checker's evaluator
(`crates/core/src/value.rs` is a different `Value`), the reference evaluator
(`crates/core/src/reference.rs`), the JS backend (JS objects and `bigint`s, docs/core.md's
representation paragraph), the bytecode and IR, the codec (it encodes the IR, not run-time
values, `crates/rt/src/codec.rs:1-17`), and every proof. Step counts and frame counts don't
change (D1253): a representation changes no call.

### 3.1 C: our own cell header (8 bytes, no weak count)

- **What.** A `Cell` pointer type in `stitchwort-rt` replacing `Rc<[Value]>`: header of a
  32-bit count, the field count and spare bits (Lean's layout: count, size, number of
  fields, tag). Its `Drop` frees through the global allocator (mimalloc, D3413) and can
  thread its work list through the freed cells instead of a `Vec` (cell-allocator.md's
  finding; `Fields::drop`, `value.rs:364-372`).
- **Cells:** 64 → 56 bytes for two fields; one load and compare fewer per uniqueness test.
- **Changes:** `value.rs` (`Fields`), `native_abi.rs` (layout constants, `sw_cell_new`,
  `free_emptied`, `probe_layout`: fewer `std` facts to check), `n1.rs` (`unique`, counts,
  `new_cell`), `cell_cache.rs` (links through the count word as now), `alloc_trace.rs`,
  `machine.rs`'s uniqueness test. The `Value` stays 24 bytes: `Data`'s length can stay in
  word 2 for now.
- **What it buys alone:** binary-trees 2–6%, others 0–2% **[estimated]**: one word less per
  cell and one load less per `Unpack`/`CtorReuse`. Its real value is that every other option
  needs it, and it makes the cell cache the free path of Rust drops too (cell-allocator.md
  stage C) without a second migration (D3414).
- **Risk:** low to medium: unsafe code we own instead of `std`'s, guarded by the existing
  agreement and trace tests.

### 3.2 E: two-word values (16 bytes)

- **What.** Put `Data`'s field count in the cell header (C already does) and `Text`'s byte
  length in its object (a thin text object of our own instead of `Rc<str>`). Then no kind
  needs word 2, and `Value` is 16 bytes: kind byte and constructor tag in word 0, payload in
  word 1.
- **What stays exactly as it is:** every number's form (the one-form rule at 2^64), `Float`
  (unboxed, D701's canonical NaN), `Tag` constructors without allocation, the constructor
  tag in the value (a `match` still reads no memory), big numbers, the self-describing value
  every generic reader in the runtime relies on.
- **Cells:** 8 + 16n. Two fields: 40 bytes (today 64, Lean 24). `Map.Tree.Bin`: 88 (136,
  Lean 48). memory-game's array: 480 MB (720, Lean 240).
- **Native code:** each register two Cranelift variables instead of three, each argument and
  result two words. On x86-64 and AArch64 a 16-byte value travels in two registers, so fewer
  spills and fewer callee-saved saves (binary-trees' 9% prologue and epilogue).
- **The machine:** a `Vec<Value>` of 16-byte registers; `run` gets faster too.
- **Changes:** `Value`'s definition and every helper in `native_abi.rs` that reads words
  (`words`, `LEN_AT`, the apply stubs, `sw_*` signatures), all of `n1.rs`'s `Val([w0, w1,
  w2])` (about 4,900 lines, mechanical but wide), `n1/runtime.rs`, `prims.rs`'s text
  natives, the effect runtime's structs (they shrink by themselves), `run.rs`, the
  standalone AOT, the tests that pin layouts and traces.
- **Risk:** medium: a wide mechanical change to unsafe code. No semantic change, so the
  differential tests (machine against native, traces, step counts) cover it completely.

### 3.3 A: one-word values

- **What.** A value is one word: an object pointer (8-byte aligned, low bits 0) or a
  scalar (low bit 1). Every heap object has C's header plus a kind.
- **Choices inside A** (a later note's to settle, with the census):
  - *Self-describing scalars or type-directed ones.* Lean and Koka don't record whether a
    scalar is a `Nat`, an `Int` or a constructor tag; the types say. Our runtime has
    generic readers (printing in tests, the effect runtime's handler matching, `Value::tag`,
    agreement tests comparing values across runners). Keeping a 2–3-bit scalar kind keeps
    them working, at the price of 61-bit small numbers. I'd keep the kind bits.
  - *Small numbers.* The one-form rule moves from 2^64 to 2^61 or 2^63: semantics
    unchanged, numbers between that and 2^64 become big. `prims::number_cost`
    (`prims.rs:429-447`) charges steps when an argument *is a big number*, so its rule must
    become "at least 2^64 in magnitude", or the counterexample search's step counts move.
  - *Floats.* Boxed as a 16-byte object wherever they are a value, or Koka's encoding:
    inline when the exponent fits the bits left, heap otherwise. Either way D701's
    canonical bits stay (the form depends only on the number). D below is what removes most
    of the boxing.
  - *Constructors with fields:* match by loading the header's tag (Lean), or carry the tag
    in the pointer's low 2–3 bits for types with few constructors (GHC, Roc).
- **Cells:** 8 + 8n: Lean's sizes. Arrays: one object with inline elements (Lean's
  `lean_array_object`), no double indirection.
- **Changes:** everything E changes, plus: every place that builds or reads a number
  (`prims.rs`, 1,271 lines; the `Nat` fast paths in `n1.rs`), the effect runtime's objects
  get headers so a word can point at them, `Fun` and closures in one allocation (overlaps
  SW-593), the alloc trace (boxed floats and mid-sized numbers become allocations, in the
  machine and native code alike), wasm32 (the playground: a 64-bit value word holding a
  32-bit pointer).
- **Risk:** high: the largest change to unsafe code, and new performance cliffs (a `Float`
  in a list allocates; numbers just under 2^64 become big).

### 3.4 D: unboxed fields chosen per type

- **What.** At lowering, a constructor field whose *declared* type is `Float` (or, under A,
  a fixed-width number type) is stored raw in a scalar area after the pointer fields (Lean,
  OxCaml's mixed blocks). The lowerer knows each constructor's declared field types even
  though the runtime IR is untyped; `Field` and `Unpack` know their constructor, so they
  know each field's kind statically. One function in `stitchwort_core` decides the layout,
  like `nat_shape` and `Data::unboxed_field`, so every backend agrees.
- **Under E it buys little:** fields are already raw words, so D only saves the kind word
  of scalar fields. **Under A it is what makes `Float` records not allocate**, and it pairs
  with nat-shaped-types.md: `Fin` becomes a scalar, so unboxed.
- **Changes:** the lowerer, `Shapes` (so the drop walk and generic readers know where the
  pointers end), reuse (same layout, not just same arity), the cell cache (keyed by size).
- **Risk:** medium; it adds a layout per constructor to everything that walks cells.

### 3.5 B: compact cells behind three-word registers

lean-runtime-speed.md's option B: fields stored as one tagged word, registers kept at three.
It gets A's footprint but none of its instruction savings, and adds a decode at every
`Field` and `Unpack` (a header load to recover the kind and tag for the register) and an
encode, sometimes an allocation, at every `Ctor`. §1.4 says the gap is instructions, so B
spends instructions to save memory. **Not recommended**, unless V1 and V3 (§5) find memory
stalls much larger than §1.4 implies.

### 3.6 How the options meet what's already built or planned

| | C | E | A (+D) |
|---|---|---|---|
| In-place reuse (`CtorReuse`, `DropReuse`), reuse across calls | same rule (same arity) | same | same size class; with D, same layout |
| Cell cache (SW-2363) | becomes the cell type's own free path, for Rust drops too | keyed by size | keyed by size |
| TRMC holes (`HoleOp::New/Fill/Take`, `ir.rs:343`) | unchanged | `Fill` stores two words | `Fill` stores one word |
| Determined fields (SW-2415) | fewer fields; compounds | compounds | compounds |
| Nat-shaped types (SW-2398) | unchanged | unchanged | `Fin` is a scalar: no cell, as `Nat` |
| One-field records unboxed (D866) | unchanged | unchanged | unchanged |
| Big numbers (SW-2302) | unchanged | unchanged | new header kind; mid-sized numbers become big |
| `Text` | unchanged | thin object | thin object |
| Arrays | unchanged | 16-B elements | 8-B elements, inline buffer |
| Effect runtime (SW-593) | unchanged | structs shrink by themselves | objects need headers; do with SW-593 |
| `probe_layout` | fewer `std` facts | fewer still | ours entirely |

## 4. How it fits the Stitchwort world

- **Proofs and the kernel** are untouched: run-time values are below the erased IR's
  semantics, and no theorem mentions them.
- **The trusted base.** The runtime and native code are trusted to run the program that was
  checked (backend-trust.md). Every option adds unsafe code that we own instead of `std`'s.
  The guard is what it is today: the machine and native code must agree on output, step
  counts, frame counts and allocation traces for every test program
  (`task test:lane AREA=native`, `AREA=rt`). A representation change that doesn't change
  meaning leaves all of these comparisons meaningful; under A, traces gain the boxed-float
  allocations on both sides.
- **Step counts and `E-RESOURCE`** (D1253) don't move, given the `number_cost` rule above.
- **The content-hash caches** hold elaborated and kernel artifacts, and an executable embeds
  the IR through the codec, whose build hash covers the runtime's sources (`codec.rs:9-11`).
  So executables are rebuilt and no cached data changes format.
- **The playground** runs the machine on wasm32; E and A change it, C only a little.
- **Migration path, each stage paying on its own:** C (header) → E (two words) → A (one
  word) with D. C and E are each complete end states; A+D is the further one. Because
  `Value`'s size is global, E and A can't hide behind a run-time switch; each is measured on
  its branch before merging, and the branch is the switch.

## 5. Verifying the bet before the big refactor

The principle: measure the thing the refactor would change, in place, before changing it,
and write down the expected number first. Every step below is cheap, uses tools we have
(`task profile:native` with `--by-instruction` and `--count-bodies`, the `call-counts`
runtime, `bench:compare --instructions`, `perf` on Overmind), and ends at a stated go/no-go.

**The decision set:** binary-trees (allocation, the headline), matcher (lists, closures,
`Map`), dijkstra (`Map`, records), octopus (lists, records), memory-game (a big array),
expressions (parser closures and effect nodes). Pidigits is excluded (its time is
`num-bigint`); scan, disk and bridge are reported but track expressions and matcher. All
ten are reported every time.

**The thresholds** (my proposal, for Matt to confirm): go on to E only if the cost model
(V4) predicts at least **1.10× on the decision set's geometric mean** against Lean (native/
Lean on the ten from 11.7 to about 10.6 or less) **and at least 1.25× on binary-trees**. Go
on to A+D beyond E only if it predicts at least another **1.10×** on the geometric mean and
the census finds boxed floats and mid-sized numbers in under 1% of field stores.

### V0: a census of values (Sonnet, 1.5 h)

- **What.** Extend the `call-counts` runtime (or a counting pass over the allocation
  trace) to record, per run: allocations by kind (cell by arity, closure, `Fun` variant,
  array, text, big number) and their bytes; the kinds of values stored into fields at
  `Ctor` (tag, `Nat` below 2^61 / 2^63 / 2^64, `Int`, `Float`, pointer, erased); peak live
  bytes; `size_of` of `Fun`, `Resume`, `Handler`. Then compute bytes allocated and peak
  under C, E and A.
- **Expect** **[estimated]**: E cuts allocated bytes 30–40%, A 55–65%, on every program
  but pidigits; floats and numbers above 2^61 are essentially absent (aoc/ and games/ use
  no `Float`, by grep).
- **Go/no-go:** if E cuts allocated bytes by less than 25% on half the decision set, drop E
  as a stage (the model goes straight from C to A).

### V1: hardware counters on Overmind (Sonnet, 1 h)

- **What.** For native and Lean, on the ten: `perf stat -e
  cycles,instructions,L1-dcache-load-misses,LLC-load-misses,dTLB-load-misses,cycle_activity.stalls_l2_miss,cycle_activity.stalls_l3_miss,cycle_activity.stalls_mem_any`,
  plus `perf stat -M TopdownL1` (Skylake). Two runs each.
- **Expect** **[estimated]**: memory-bound stall share of native cycles 25–40% on
  binary-trees, 5–15% on the AoC programs; Lean's memory-game far above both.
- **Go/no-go:** if native's memory-stall share is under 10% on every decision program but
  binary-trees, the footprint half of the bet is worth under about 5%; V4 then rests on
  instructions alone, and B is ruled out for good.

### V2: the instructions that exist because a value is three words (Opus, 1.5 h)

- **What.** On Overmind, `perf record -e instructions:u` (precise, sampled by count) on the
  decision set's native executables, folded through `--pc-map` into bytecode instructions
  and parts (SW-2332). Classify each retired instruction in generated code: a load or store
  of word 1 or 2 of a value, a spill or reload, a callee-saved save or restore, the weak
  count, everything else. For the runtime side, the same for `sw_drop_words`'s walk,
  `Value::clone`, the apply stubs' argument copies. Then count what C, E and A leave of each
  class (by rule: E removes word-2 traffic and about a third of spills and saves; A removes
  words 1 and 2 except where a scalar must be decoded).
- **Expect** **[estimated]**: value-width work is 8–15% of native instructions on the
  decision set, 15–25% on binary-trees.
- **Go/no-go:** if it is under 5% on the decision set's mean, stop after C: no full
  refactor can reach the threshold.

### V3: make cells bigger, see what it costs (Opus, 1.5 h, a throwaway branch)

- **What.** A "dilation" experiment, the cheapest in-place test of footprint: on native
  code's fixed-size cell path (`sw_cell_new`, `new_cell`, the cell cache), allocate each
  cell with 40 spare bytes after its fields, which nothing reads or writes. The fat
  pointer's length stays `n`, so no instruction changes; only the footprint grows, by the
  same 40 bytes A would remove from a two-field cell. (Freeing with the smaller layout is
  sound only because mimalloc's `free` ignores the size: measurement branch only, never
  merged.) Run at +24 B and +40 B to see whether the cost is linear. Check with `perf` that
  instructions moved under 1%.
- **Expect** **[estimated]**: +40 B costs binary-trees 8–20% of cycles, matcher, dijkstra
  and octopus 2–6%, expressions 1–4%.
- **Go/no-go:** under 3% on the decision set's geometric mean at +40 B means footprint is
  worth under 3% to A: A must then be justified by V2's instructions alone.

### V4: the cost model and the decision (Opus, 1 h, paper)

- **What.** Per program, predicted time under each option = today × (1 − w × s) × f, where
  `w` is V2's value-width share of instructions, `s` the share of it the option removes, and
  `f` the footprint factor from V3's slope times V0's bytes removed. Discount by the SW-2363
  lesson (removed instructions save less than their share where dependent chains set the
  pace): use V1's rate per program. Check it against Lean's per-node counts on
  binary-trees.
- **Decision:** the thresholds above. Record the predictions on the tickets, so each stage's
  merge can be judged against them.

### Optional V2b: a Rust model of binary-trees (Sonnet, 1 h)

The same `make`/`check` hand-written in Rust with 64-, 40- and 24-byte nodes, mimalloc and
the same free-list cache. It bounds the representation's effect with ideal code generation,
as C13 did for `Set`; it doesn't say what Cranelift will do. Only if V2 and V3 disagree.

### After the decision: each stage judged against its prediction

| Stage | Lanes | Measured by | Kept if |
|---|---|---|---|
| C, the header | Opus, 4–6 h | `bench:compare --instructions` on Overmind, before and after | no program over 1% slower. Kept even if neutral: E and A need it |
| E, two words | Opus, 10–16 h (could split: runtime, then `n1.rs`) | the same, plus V1's counters | at least 60% of V4's predicted gain; otherwise not merged, and the model is recalibrated before A is considered |
| D on E (floats only) | Sonnet, 3–4 h | a `Float` benchmark (new) | skip unless a program needs it |
| A with D | Opus, 25–40 h, its own design note first (the choices in §3.3) | as E | as E, against V4's prediction for A |

**Where to stop if it doesn't pay:** after V2 (under 5%: keep nothing, the note is parked);
after V4 (under the threshold: do C only); after E (under 60% of prediction: keep C, revert
E). Stopping at any point leaves nothing half-done: C and E are complete end states.

**Time:** V0–V4 are about 5–6.5 lane-hours, about one day with two lanes in parallel (V0
and V1 together, V2 and V3 together; V3 and V1 need a quiet Overmind). The full refactor, if
every gate passes, is about 40–60 lane-hours **[estimated]**.

**When:** the measurements are cheap and can run now, but the decision should use V4 rerun
on `main` when it's made. The levers already planned remove whole allocations and calls
(operations in place stages D and E: up to 1.3–1.5× on the parsers, SW-2417; specialising
capturing closures, SW-2135; the cheaper call protocol, SW-2322), and as they land, the
share that representation decides will grow.

## 6. Recommendation

**The problem.** Every list cell, tree node and record our native programs build is about
2.7 times the size of Lean's, and every value travels as three machine words. But the
measurements say most of our gap to Lean is the number of instructions we run (11.3× of the
11.7×), not memory stalls (1.04×) **[derived from measured counts]**. So the size of
values matters through the extra work it causes, more than through the cache.

**The change.** In three steps, each worth having alone: (C) our own 8-byte cell header
in place of `Rc`'s 16; (E) two-word values, by moving the two lengths the third word holds
into the objects, which changes no number, float or tag; then, only if the measurements
justify it, (A) one-word values with floats unboxed in typed fields (D), as Lean does.
Before any of it, about 5–6 lane-hours of measurement (§5) with go/no-go points written
down first.

**What it should do** **[all estimated, to be replaced by V4's numbers]**: C: 1.01–1.03× on
the geometric mean against Lean (binary-trees 2–6%). C+E: 1.05–1.12× (binary-trees
1.15–1.3×, the `run` interpreter faster too). A+D on top: another 1.05–1.10×. That's
native/Lean from 11.7 to about 10.5 after E, and about 9.5–10 after A, with today's other
gaps unchanged. It is a real but secondary lever: the parsers' effect machinery and
unspecialised closures are bigger, and get bigger shares as they are fixed.

*Superseded by V4 (§7.6):* C is about 1.01×, not 1.01–1.03×; C+E's and A's estimates hold
at their middles (1.09× and another 1.08×), which is just under the gate.

### Open questions for Matt

- **Is C then E the end state, with A+D held back until the measurements justify it?**
  Recommendation: yes. E keeps everything we like about today's values (no boxing, 64-bit
  numbers, tags without a memory read, values that describe themselves) and takes the cheap
  half of the saving. A's extra half costs float boxing and new performance cliffs, and the
  evidence so far says memory isn't where we lose.
- **Are the thresholds right: at least 1.10× predicted on the geometric mean and 1.25× on
  binary-trees before E, and another 1.10× before A?** Recommendation: yes; they're the
  size of gain that would show in the headline table, and E's work (10–16 h) is about what
  other levers of that size cost.
- **Run the measurements (V0–V3) now, or after operations in place stage D lands?**
  Recommendation: now. They're cheap, V1 and V2 also inform SW-2322 and stage D, and V4 is
  rerun at decision time anyway.
- **Should option B (compact cells, three-word registers) be dropped from consideration?**
  Recommendation: yes, unless V1 and V3 find memory stalls far larger than §1.4 implies.

### Calls I made (implementation, reversible)

- Adding option E, which wasn't in lean-runtime-speed.md.
- The decision set (six programs) and leaving pidigits out of it.
- Putting the header (C) first and keeping it even if neutral.
- Self-describing scalars as my default inside A, for the generic readers.

## 7. V4: the model and the decision

SW-2429, 8 Nov 2026, Opus, paper lane (nothing built or run). It combines V0
([SW-2425](../reviews/SW-2425-value-census.md)), V1
([SW-2426](../reviews/SW-2426-hardware-counters.md)), V2
([SW-2427](../reviews/SW-2427-value-width-instructions.md)) and V3
([SW-2428](../reviews/SW-2428-dilation.md)), with the times of SW-2295's latest run
(`e11c7b3c2`). The arithmetic is a 60-line script kept in the lane's scratchpad; every input
is in the tables below, so it can be redone by hand.

### 7.1 The model

For each program and option, the share of cycles saved is

    S = k × I + F + W,    predicted speed-up = 1 / (1 − S)

- **I, instructions removed** (V2, shares of *all* retired instructions, cumulative: E
  includes C's weak count, A includes E's word 2):
  - generated code by V2's rule (word 2, the weak count, a third of stack traffic and
    callee-saved saves for E, two thirds and word 1 too for A) **[measured classes, rule
    estimated]**;
  - plus a share m of V2's register-move column (low 0, central ½, high all);
  - plus a share r of V2's runtime bound (drop walk, apply stubs, `Value::clone`): low 0,
    central 0.3, high 0.6. V2 says the drop walk rarely touches word 2, so the bound is well
    above the truth for E.
- **k, how much time a removed instruction was worth**, calibrated where instructions and
  time have both moved **[measured pairs, ratios derived]**:

  | Change | instructions | time | k = time saved ÷ instructions removed |
  |---|---:|---:|---:|
  | SW-2363, cell cache, binary-trees (mimalloc's fast path removed) | −30.5% | −10.6% | 0.35 |
  | Same change, SW-2295's runs (13:28 → 17:58) | −26.4% | −7.1% | 0.27 |
  | SW-2394/2396, dijkstra over a cost table | −57.2% | −51.8% | 0.91 |
  | SW-2349, operations in place stage B, expressions | −37.1% | −34.1% | 0.92 |
  | SW-2323/SW-2391 era, matcher | −12.2% | −14.3% | 1.17 |
  | bridge, same run | −19.2% | −19.2% | 1.00 |
  | SW-2337, Parse stage 2, scan | −8.6% | −10.6% | 1.23 |

  - Removing *whole work* (calls, branches and the loads they wait on) is worth about its
    share: k ≈ 0.9–1.2.
  - Removing *cheap, independent* instructions beside a slow dependent chain is worth about
    a third: k ≈ 0.3 (SW-2363's lesson).
  - SW-2433 (sharing `JumpK`) and SW-2421 (the drop worklist) moved instructions only, with
    no time measured, so they don't calibrate k. What they do show: an allocation and its
    free cost about 140 instructions (SW-2433: 2.66 G for 18.6 M), about 1% of the parsers;
    1.3 GB fewer bytes allocated showed nothing beyond those instructions; and mimalloc's
    small path is cheaper than any clever replacement tried (SW-2421: +3–4%).
  - What E and A remove is mostly the cheap kind: spills and reloads that hit L1,
    callee-saved pushes and pops, register moves (which Skylake mostly eliminates at
    renaming). Some reloads sit on a dependent chain, and binary-trees' high backend share
    (26% against Lean's 4%) may be the store port, where removed spill stores are worth
    more. So **k: low 0.3, central 0.6, high 1.0** **[estimated]**.
- **F, footprint**, only where V1 shows memory stalls above Lean's (binary-trees and
  memory-game); elsewhere V3 measured ±1% at +40 B, so F is 0 (high case: 1% for E, 1.5% for
  A) **[measured flatness; small high case estimated]**.
  - *binary-trees.* V3's cost is convex in the cell's size: +32 B of size class (64 → 96)
    cost +20.2% of cycles, +48 B (64 → 112) +35.0%. A curve through those points gives about
    −7% of cycles for E's −24 B (64 → 40), and the straight line to K = 24 gives −15%. A
    second bound: native's memory stalls are 23.1% of cycles against Lean's 8.2% (V1), so
    shrinking to Lean's 24-byte cells can remove at most about 15 points; E goes 24 of the
    40 bytes of the way. So **E: 5 / 9 / 15%, A: 10 / 15 / 20%** of cycles **[derived from
    measured points; extrapolation estimated]**. V3's wall time grew more than its cycles
    (+61% against +35%), but that was kernel time that appeared *with* the bigger cells
    (about 0.07–0.17 s at K = 0, 0.6 s at K = 24, 0.8 s at K = 40; the range at K = 0 is from
    not knowing the clock), so shrinking cells can't remove much of it. I don't count it.
  - *memory-game.* V3 didn't dilate its 720 MB array (only cells). Native's stall cycles
    are 2.0 G against Lean's 0.85 G, an excess of about 8% of native's cycles (V1); that's
    the most any footprint change can remove. A random access touches one line however wide
    the element, so shrinking the array 720 → 480 MB (E) or 240 MB (A) removes only part of
    it: **E: 1 / 3 / 5%, A: 2 / 5 / 8%** **[estimated]**.
- **W, store-forwarding stalls** on expressions and scan (SW-2432's finding in V2):
  native's backend share is 17.5–18% of slots against Lean's 2–3%, with the store buffer
  full 6% of cycles and 11 blocked forwards per 1000 instructions. If the cause is values
  copied with one width and read with another, a 16-byte value may copy as one store and
  one load. **E: 0 / 3 / 8%, A: 0 / 4 / 10%** of cycles on those two **[estimated; the cause
  is an inference not yet traced]**.
- **Programs V2 didn't measure:** disk and bridge take matcher's figures; pidigits is 0
  (its time is `num-bigint`).

### 7.2 Predictions

Speed-up of native code, low / central / high **[estimated by the model above from measured
inputs]**:

| Program | C | E (C+E) | A (C+E+A) | A beyond E |
|---|---|---|---|---:|
| binary-trees * | 1.02 / 1.03 / 1.06 | 1.09 / **1.21** / 1.46 | 1.19 / 1.44 / 2.03 | 1.19 |
| matcher * | 1.00 / 1.00 / 1.00 | 1.02 / **1.06** / 1.14 | 1.04 / 1.12 / 1.30 | 1.06 |
| dijkstra * | 1.00 / 1.00 / 1.01 | 1.02 / **1.06** / 1.15 | 1.05 / 1.14 / 1.34 | 1.07 |
| octopus * | 1.00 / 1.00 / 1.01 | 1.02 / **1.06** / 1.13 | 1.04 / 1.13 / 1.30 | 1.07 |
| memory-game * | 1.00 / 1.01 / 1.02 | 1.03 / **1.09** / 1.19 | 1.06 / 1.18 / 1.40 | 1.08 |
| expressions * | 1.00 / 1.00 / 1.00 | 1.01 / **1.06** / 1.19 | 1.01 / 1.11 / 1.34 | 1.05 |
| scan | 1.00 / 1.00 / 1.00 | 1.01 / 1.06 / 1.20 | 1.01 / 1.11 / 1.36 | 1.05 |
| disk (matcher's figures) | 1.00 / 1.00 / 1.00 | 1.02 / 1.06 / 1.14 | 1.04 / 1.12 / 1.30 | 1.06 |
| bridge (matcher's figures) | 1.00 / 1.00 / 1.00 | 1.02 / 1.06 / 1.14 | 1.04 / 1.12 / 1.30 | 1.06 |
| pidigits | 1.00 | 1.00 | 1.00 | 1.00 |
| **decision set, geometric mean** | 1.004 / 1.008 / 1.015 | 1.03 / **1.09** / 1.21 | 1.07 / 1.18 / 1.43 | **1.08** |
| all ten, geometric mean | 1.002 / 1.005 / 1.010 | 1.02 / 1.07 / 1.17 | 1.05 / 1.14 / 1.35 | 1.07 |

`*` the decision set. "A beyond E" is the central A over the central E.

**Which input decides it.** Moving one input from its low to its high value, the others
central (E, decision-set geomean and binary-trees):

| Input | geomean, low → high | binary-trees, low → high |
|---|---|---|
| k (worth of a removed instruction) | 1.06 → 1.14 | 1.15 → 1.30 |
| F (footprint) | 1.08 → 1.11 | 1.16 → 1.31 |
| m (register moves) | 1.08 → 1.10 | 1.19 → 1.23 |
| r (runtime side) | 1.08 → 1.10 | 1.21 → 1.21 |
| W (store forwarding) | 1.08 → 1.10 | 1.21 → 1.21 |

The uncertainty is dominated by **k times V2's "a third of the spills and saves" rule**: the
two multiply, and only E's actual register count tests the rule. On binary-trees, footprint
counts almost as much. E clears the gate on both counts at k ≥ 0.8.

**Check against Lean's per-node counts** (§1.4): binary-trees runs about 315 instructions
per node against Lean's 143. E removes 36 of them by the rule (52 with register moves), A 65
(96): inside the 20–50 the note guessed for E. After A, native would still run about 1.5×
Lean's instructions on binary-trees, so a 2× high case for A is the edge of plausible, not
the middle.

### 7.3 The gate

The gate (D3432): E only if V4 predicts at least 1.10× on the decision set's geometric mean
and at least 1.25× on binary-trees; A beyond E only if another 1.10×.

- **E, geometric mean:** (1.211 × 1.058 × 1.063 × 1.056 × 1.091 × 1.060)^(1/6) = e^(0.509 / 6)
  = **1.088**. Below 1.10.
- **E, binary-trees:** S = 0.6 × (11.5 + ½ × 5.0 + 0.3 × 0.1) + 9 = 17.4% of cycles, 1 / (1 −
  0.174) = **1.21**. Below 1.25.
- **A beyond E:** 1.18 / 1.09 = **1.08**. Below 1.10. (A's other condition, boxed floats and
  mid-sized numbers in under 1% of field stores, passes: V0 found none.)

**So by the rule as written, E does not go, narrowly**: the central prediction is 1.09
against 1.10 and 1.21 against 1.25, and the range (1.03–1.21, 1.09–1.46) straddles both
lines. A beyond E misses too. C passes its own test trivially (it is kept if nothing is over
1% slower) but predicts only about 1% on the mean.

**Estimates the measurements overturned.** The note's C (1.01–1.03× on the mean) is about
1.005–1.015×; its C+E (1.05–1.12×, binary-trees 1.15–1.3×) and A beyond E (1.05–1.10×) hold,
at their middles. V3's footprint estimates were wrong both ways (binary-trees bigger, the
rest smaller; SW-2428). V1's binary-trees stall share (23%) was just under its estimate.

### 7.4 What it would mean against Lean and CPython

Geometric means over the ten, from SW-2295's latest run, with today's other gaps unchanged
**[derived from the predictions]**:

| | today | C | E (low / central / high) | A (low / central / high) |
|---|---:|---:|---|---|
| native / Lean | 11.7 | 11.6 | 11.4 / **10.9** / 10.0 | 11.1 / **10.2** / 8.7 |
| native / CPython | 2.8 | 2.8 | 2.7 / **2.6** / 2.4 | 2.65 / **2.4** / 2.1 |

binary-trees against Lean goes from 2.85× to about 2.35× under E and about 2.0× under A.
The parsers stay at 71–73× Lean under E: their gap is effect machinery and allocation
count (SW-2417), which value width barely touches.

### 7.5 Cheaper changes the measurements point to

Each on the same model (share of cycles saved, low / central / high) **[estimated]**:

| Change | Where it pays | Decision-set geomean | Largest single gain (central) | Work |
|---|---|---|---|---|
| **SW-2431**, huge pages for native's heap | binary-trees, memory-game: page walks and page faults | 1.002 / **1.009** / 1.023 | binary-trees, memory-game 1.03 | 45 min, maybe only a mimalloc option |
| **SW-2437**, copy runtime values with matching widths | expressions, scan (store buffer, blocked forwards); a little on matcher, dijkstra | 1.000 / **1.009** / 1.025 (all ten 1.011) | expressions, scan 1.04 (up to 1.11) | 1 h |
| **weak-count load** (the part of C that costs instructions) | binary-trees | 1.002 / **1.005** / 1.013 | binary-trees 1.02 | 30 min |
| **SW-2434**, erased fields not stored | matcher (24% of its fields), octopus | 1.000 / **1.002** / 1.009 | matcher 1.01 (up to 1.03) | 1 h to find, then lowering |
| **SW-2422**, allocation by cause | expressions, scan | (a measurement, not a change) | | running |

Notes on each:

- **Huge pages.** The dTLB ratio is striking (580–1100× Lean's), but the count is small: 1.5
  M page walks on binary-trees and 1.0 M on memory-game, at 30–100 cycles each, are 0.2–1.8%
  of their cycles. The rest of the possible gain is kernel page-fault time, which V1's
  user-space counters don't see. V3's kernel time growing from about 0.1 s to 0.8 s as cells
  grew suggests mimalloc returns and refaults pages; SW-2431 should try mimalloc's large-page
  and purge-delay options, which need no rebuild, before anything else.
- **Store forwarding** is the one alternative aimed at the parsers, where E does least. It
  overlaps E's W term: if it lands first, E's prediction on expressions and scan drops by
  about the same amount.
- **The weak-count load** is a lower bound in V2 (the compare isn't counted). C makes it moot;
  done alone it is worth it only if C is weeks away, which it is if E waits.
- **Erased fields** pay most if dropping one turns a two-field cell into a one-field record,
  which D866 already unboxes: then a whole allocation (about 140 instructions, SW-2433) goes,
  not just a slot. It composes with every width.
- **SW-2422** is the input for the levers bigger than any of these on the parsers:
  operations in place stages D and D+E, bounded at 1.25–1.5× on expressions and scan
  (SW-2417), against E's 1.06 there.

Together the four changes predict about **1.025× on the decision-set geomean (central) for
about 4 hours**, against C+E's 1.09× for 14–22 hours: similar gain per hour, with far less
risk, and none of it waits on a gate. They should go before E. They take a little of
E's gain with them (store forwarding on the parsers, the weak count, a little footprint on
binary-trees), so E's central prediction after them is about 1.08× on the mean.

**One measurement would settle the gate cheaply.** k and V2's rule decide it, and only E's
register count tests them directly. A throwaway "register dilation" branch (the mirror of
V3) would: native code carrying a fourth, unused word in every register, argument and
result, kept live across calls so Cranelift can't drop it. What a fourth word costs is close
to what removing the third saves (a little more, since register pressure is convex). If it
costs at least about 11% of binary-trees' cycles and 6–7% on the decision set's mean, E
clears the gate. Opus, 2–4 h **[estimated; how mechanical adding a word to `n1.rs`'s
`Val([w0, w1, w2])` is wasn't checked]**.

### 7.6 Recommendation

**The problem.** Our run-time values are three machine words, and our cells 2.7 times
Lean's. The four measurements agree on where that costs: on binary-trees, both in
instructions and in waiting for memory; everywhere else, almost only in extra instructions,
mostly spills and register saves (7% of instructions under E's rule, measured), while
memory size itself is worth under 1% outside binary-trees and memory-game (measured).

**The change.** Don't start two-word values (E) yet. First the four cheap changes in §7.5
(huge pages, value copies with matching widths, the weak-count load, erased fields), about
4 lane-hours. Then rerun this model on `main` once operations in place stage D and
SW-2422's cuts have landed, which make value width a larger share of what's left, with the
register-dilation experiment if the answer is still close.

**What it should do.** The cheap changes: about 1.025× on the decision set (estimated),
mostly on binary-trees, memory-game and the parsers. E, if built today: about 1.09× on the
decision set and 1.21× on binary-trees (estimated, range 1.03–1.21× and 1.09–1.46×), native
against Lean from 11.7× to about 10.9×; just short of the 1.10× and 1.25× the gate asks
for. One-word values (A) beyond E: about 1.08× more (estimated), also short.

**The decision for Matt.** Hold E (and A) below the gate, do the four cheap changes now,
and rerun V4 after operations in place stage D, rather than lowering the gate or building E
on a prediction that straddles it? **Recommendation: yes.** E's prediction is close enough
that one 2–4 h experiment, or the rerun, could flip it; 10–16 hours of wide unsafe change on
a coin-flip is the kind of refactor the note set out not to commit to. C (the header) waits
with E, since alone it is worth about 1% and the weak-count change takes most of that for
30 minutes.

### 7.7 Calls I made (implementation, reversible)

- k's range (0.3–1.0, central 0.6) from the calibration table; register moves at half and
  the runtime side at 0.3 of V2's bound in the central case.
- binary-trees' footprint from V3's convex curve and V1's stall excess, not V3's straight
  line; V3's kernel time left out of what shrinking saves.
- disk and bridge on matcher's figures; pidigits at 1.00.
- Means over the six-program decision set, as the gate says, with all ten shown beside.

## 8. Not done, and findings

**Not done:** nothing was built, run or profiled. Every share is from the reports cited;
every effect is an estimate. Lean's header and Koka's float boxing were read from their
sources; OCaml, GHC, Swift, MLton, Roc and Chez details are from memory and marked so. The
mimalloc size classes at 24, 40 and 56 bytes weren't checked.

**Findings worth filing:**

- **Weak counts are never used** (no `Weak` in `crates/rt`), yet every native uniqueness
  test loads and compares one (`n1.rs:4629-4635`). Until C lands, the test could compare
  only the strong count if the runtime never creates a `Weak`, with a debug assertion and a
  note in `probe_layout`. A one-load win on every `Unpack` and `CtorReuse`; Sonnet, 30 min.
  (C makes it moot; worth it only if C is more than a few weeks away.)
- **`prims::number_cost` is tied to representation** ("an argument is a big number",
  `prims.rs:441-446`). Any change to where big numbers start (A) must restate it by
  magnitude. A comment now saves a surprise later; no ticket needed beyond a note on A's.
- **The instruction-rate table (§1.4) is worth adding to every comparison run**:
  `compare.py` has times and instructions for both runners, so instructions per second and
  the ratio of rates are one division each, and say at a glance whether a program's gap is
  work or waiting. Sonnet, 20 min.

## 9. Evidence outside the decision set: rbmap's node (9 Nov 2026, SW-2472)

A measurement, run after §7 was written; nothing in the runtime was changed. It
asks why `bench/compare/rbmap`'s tree node takes about 160 bytes in a native run
against Lean's 48, and what each option does to it. rbmap and rbmap-ck are not in
the decision set (§5, V4), so §7's numbers and gate are untouched; this section is
only evidence for Matt to weigh against them.

### 9.1 Method

- **Peak RSS from slopes.** `stitchwort build --native --no-cache` on
  `bench/compare/rbmap/main.sw` (release build with `stitchwort-cli/dev`), run at several
  sizes under `/usr/bin/time -l` (maximum resident set size, macOS). The bytes per node
  are the slope between sizes, so the runtime's and the allocator's fixed costs drop out.
  The same for `rbmap-ck` (every version kept; the count is the number of inserts), for
  `binary-trees`, and for Lean's own executables built from `bench/compare/lean`
  (`lake build rbmap rbmap_ck binary_trees`).
- **What the census can and can't say.** The `value-census` feature counts the bytecode
  machine's allocations (`stitchwort run`), not native code's, so it was used for what a
  node holds, not for bytes: a run of rbmap at 200,000 inserts under
  `--features stitchwort-rt/value-census`. Its model sizes are the formulas of
  `value_census.rs`, without allocator rounding.
- **Lean's node** from the C that `lean -c` emits for `Compare/Rbmap.lean`: every node is
  `lean_alloc_ctor(1, 3, 2)`, and the colour and the flag are set with `lean_ctor_set_uint8`.

### 9.2 Measured

| Program | Sizes | Peak RSS | Slope |
|---|---|---:|---:|
| rbmap, native | 0 / 500k / 1M / 2M inserts | 3.26 / 83.6 / 163.8 / 324.4 MB | **160.5 B per node** (500k to 1M: 160.5; 1M to 2M: 160.5) |
| rbmap, Lean | 500k / 1M / 2M | 28.7 / 52.8 / 100.9 MB | **48.1 B per node** (1M to 2M) |
| rbmap-ck (every version), native | 100k / 200k / 400k | 376 / 798 / 1,689 MB | 4,213 B (100k to 200k), **4,454 B (200k to 400k)** per insert |
| rbmap-ck, Lean | 100k / 200k / 400k | 117.8 / 245.3 / 514.7 MB | 1,275 B, **1,347 B** per insert |
| binary-trees, native | depth 14 / 16 / 18 / 20 | 7.4 / 20.1 / 70.5 / 302.5 MB | 64.4 B (14 to 16), 64.2 B (16 to 18), 73.7 B (18 to 20) per node |
| binary-trees, Lean | depth 16 / 18 / 20 | 9.0 / 21.5 / 102.8 MB | 16 B (16 to 18), 25.8 B (18 to 20) per node |

- rbmap holds exactly the tree at its peak: the census at 200,000 inserts allocates 200,000
  five-field cells and has 200,005 live at its peak, because the tree is updated in place
  (6.4 M `CtorReuse` refills). So the slope is the node, with no side objects: the extra
  0.5 B is page granularity.
- rbmap-ck makes 27.8 nodes per insert natively (4,454 / 160) and 28.1 in Lean (1,347 / 48):
  the same path copying, so the ratio of its footprint to Lean's (3.3×) is the node's ratio
  (3.3×), nothing else.
- binary-trees' peak holds about 4 × 2^depth nodes (the stretch tree, or the long-lived
  tree plus one fresh tree), the figure used for the per-node slopes. Native's 64 B is
  exact for depths 14 to 18; at depth 20 it reads 73.7 B, which I did not explain (more
  than one tree alive at once, or the allocator keeping freed pages, are the candidates).
  Lean's two intervals disagree (16 and 26 B) for the same reason of peak composition,
  so treat Lean's binary-trees per-node figure as roughly 24 B (the formula's), not as
  measured to the byte.

### 9.3 One node, word by word

A `Node color left key value right` is an `Rc<[Value]>` of 5 fields (`native_abi.rs`:
`STRONG_AT`, `WEAK_AT`, `RC_VALUE_AT`, `VALUE_SIZE`; the census confirms the stored
kinds: `Color` and `Bool` are `Tag` values (no allocation), the key a `Nat` under 2^61,
the subtrees `Data` or `Tag` (for `Leaf`)). 16 + 5 × 24 = 136 bytes, and mimalloc
gives it a 160-byte block:

| Words | Bytes | What |
|---|---:|---|
| 0 | 8 | strong count (the one word with information) |
| 1 | 8 | weak count: always 1, never read for its value (§8's first finding) |
| 2, 3, 4 | 24 | `color`: kind byte `TAG_TAG` and the constructor's tag (Red or Black) in word 0; word 1 (payload) and word 2 (length) unused |
| 5, 6, 7 | 24 | `left`: kind and constructor tag; the pointer; the child cell's field count (5) |
| 8, 9, 10 | 24 | `key`: kind `TAG_NAT`; the number (not boxed); length unused |
| 11, 12, 13 | 24 | `value`: a `Tag` as `color`: one bit of information in 24 bytes |
| 14, 15, 16 | 24 | `right`: as `left` |
| 17, 18, 19 | 24 | mimalloc's rounding: 136 B is 17 words, and its size classes above 64 B go 80, 96, 112, 128, 160, 192, ... |

Sorted by what the bytes are:

| | Bytes | Share |
|---|---:|---:|
| information: strong count, two subtree pointers, the key (and 2 bits of colour and flag) | 32 | 20% |
| kind and constructor-tag words (5 fields) | 40 | 25% |
| length words (5 fields; 2 meaningful when the child is a node, the rest zero) | 40 | 25% |
| unused payload of `Tag` fields (colour, flag) | 16 | 10% |
| weak count | 8 | 5% |
| allocator rounding | 24 | 15% |
| | 160 | |

Lean's node is 8 (header) + 3 × 8 (left, key, right: a `Nat` is a tagged word) + 2 (colour
and flag as scalar bytes) = 34, which Lean's allocator takes at 40 or 48. The measured 48.1 B
per node says 48: presumably 40 plus an 8-byte allocator header in the build the Nix `lean`
gives (I did not look). Compared with the measured Lean node, the 160 B is 3.3×; the
information bytes are the same in both. Everything above those is the value format.

### 9.4 What each option would make the node

The sizes below are formula plus mimalloc's classes (bins of 8 bytes up to 64, then 80, 96,
112, 128, 160, 192, 224, 256; I inferred the 160 from the slope above, not by calling
`mi_good_size`). "At 2M" is the rbmap peak at 2M inserts, node bytes only (about 3 MB
fixed on top). "Toward Lean" is node size against Lean's measured 48.

| Layout | Formula | Bytes | Block | rbmap at 2M | vs Lean's 48 | rbmap-ck at 2M inserts (est.) |
|---|---|---:|---:|---:|---:|---:|
| today **[measured]** | 16 + 5 × 24 | 136 | **160** | 321 MB (324 measured) | 3.3× | ~9.6 GB |
| **C**: 8-byte header | 8 + 5 × 24 | 128 | **128** | 256 MB | 2.7× | ~7.7 GB |
| **E**: two-word values | 8 + 5 × 16 | 88 | **96** | 192 MB | 2.0× | ~5.8 GB |
| **A**: one-word values | 8 + 5 × 8 | 48 | **48** | 96 MB | 1.0× (Lean measured 101 MB) | ~2.9 GB |
| D alone: colour and flag as bytes after the fields, today's header and 24-byte values | 16 + 3 × 24 + 2 | 90 | **96** | 192 MB | 2.0× | ~5.8 GB |
| C + D | 8 + 3 × 24 + 2 | 82 | **96** | 192 MB | 2.0× | ~5.8 GB |
| E + D | 8 + 3 × 16 + 2 | 58 | **64** | 128 MB | 1.3× | ~3.8 GB |
| A + D (Lean's layout) | 8 + 3 × 8 + 2 | 34 | **40** | 80 MB | 0.83× | ~2.4 GB |

The rbmap-ck column is the node ratio times about 60 M nodes (2 M inserts at about 30
per insert; 27.8 measured at 400k, rising 1.5 per doubling **[extrapolated]**); today's
figure is why rbmap-ck cannot run at Lean's size, and its row for A is Lean's real
footprint (about 2.9 GB, **[estimated]**).

What this says that the earlier sections didn't:

- **Mimalloc's size classes change C's value for this node.** §3.1 and §7 count C as one
  word of 64 or 136 bytes (6%). Here 136 becomes 128, an exact class: a 20% smaller block,
  four times the percentage, and the same for any five-field cell (`Map.Tree.Bin` is 136 B
  too). Two-field cells don't get it (64 to 56 is exactly the word). The unchecked
  classes §8 mentions: 24, 40 and 56 are exact (8-byte steps to 64), so binary-trees
  gets C 56, E 40, A 24 with no rounding loss, and its measured 64 B today is exact.
- **E and D reach the same node.** A five-field node is only partly pointers, so E's 33%
  cut in a cell is the same 160 to 96 as storing the two enum fields as bytes (D). E and D
  together (64 B) get within 1.3× of Lean. This is the one case where D is worth saying
  separately: it needs no change to value width, only the lowerer's per-constructor
  layout (§3.4, "medium" risk), and gets 160 to 96 here. Under today's layout it does
  nothing for binary-trees (no scalar fields).
- **An unboxed small `Nat` alone does nothing.** The key is already a raw word in the
  `Nat` value's payload; what costs is the kind word beside it, which only a narrower
  value (E, A) removes. A type-directed raw `Nat` field would need a fallback for big
  numbers, which is A's problem, not a smaller step.
- **Only A reaches Lean's size on this node.** A gives 48 B, the same as Lean's measured
  48; A + D gives 40, which would beat Lean's measured figure if Lean's extra 8 bytes are an
  allocator header we wouldn't pay.

### 9.5 Would this change the V4 decision?

The decision (§7.6: hold E and A, do the cheap changes, rerun V4 after operations in
place stage D) is about **speed on the six-program decision set**; this evidence is about
**memory on programs outside it**, and §7 found memory size worth under 1% of time outside
binary-trees and memory-game. So it does not move E's or A's predicted speedup, and the
gate (1.10× and 1.25×) is no nearer.

What it does change, for Matt to weigh:

1. **A reason, other than speed, to value width.** rbmap-ck at Lean's size (2 M kept
   versions) needs about 9.6 GB today and cannot run on the comparison machines; E would
   need about 5.8 GB, A or E + D 2.4 to 3.8 GB. If "rbmap-ck at Lean's size" matters as a
   comparison (README.md says the size was cut to 400k for this reason), only A or E + D
   gets there; C alone does not. That is a scope question (what the comparison suite is
   for), not a measured speed one.
2. **C is worth more than §3.1 says on five-field cells,** by a rounding accident: 20% of
   the footprint of rbmap's and `Map`'s nodes. It was already the stage everything else
   needs; this adds a reason to do it early but nothing about order.
3. **D (enum fields as bytes) deserves its own estimate.** It is the one cheaper step that
   cuts a five-field node by 40% without changing width, and it is not in §7.5's list of
   cheap changes. It touches the lowerer, the shapes and reuse (§3.4), so it is not 30
   minutes; but how common enum fields in large cells are is unknown. Count them with the census (field kinds
   `tag` in cells with five or more fields) before judging.

**My reading:** it doesn't change the V4 decision as it was asked (speed on the decision
set), and the recommendation to hold E stands. It does add a second, separate question for
Matt: whether Lean-sized memory on tree benchmarks is a goal, since that, and not the
timing gate, is what decides between E and A (or E + D) for rbmap-ck. I did not change the
recommendation.

### 9.6 Uncertainties

- The 73.7 B at binary-trees depth 20 and Lean's 16 vs 26 B at binary-trees are
  unexplained; the figures used are the 16 to 18 interval (native) and the formula (Lean).
- Lean's node: the code says 34 bytes, the slope 48.1; the 8-byte difference is a guess
  (allocator header), not checked against Lean's runtime.
- Mimalloc's classes above 64 B are inferred from the 160.5 B slope and mimalloc's
  documented bin spacing, not from calling `mi_good_size`. The rounded sizes for E (96),
  D (96) and E + D (64) rest on the same table.
- RSS counts pages touched: it includes the kernel's page rounding and free memory the
  allocator holds, which the slope averages out at the sizes used but not exactly.
- The rbmap-ck column at 2 M is an extrapolation from 100k-400k; only its ratios to
  today's figure are firm.
- Nothing was timed: no speed claim is made here.

## Sources

- Lean 4 `src/include/lean/lean.h` (master, fetched 8 Nov 2026): `lean_object`,
  `lean_box`, `lean_ctor_set_uint32`, `lean_array_object`.
- Koka `kklib/include/kklib/box.h` (dev, fetched 8 Nov 2026): `kk_box_t`, `KK_BOX_DOUBLE64`.
- S. Marlow, A. R. Yakushev, S. Peyton Jones, "Faster laziness using dynamic pointer
  tagging", ICFP 2007.
- D. F. Bacon, S. J. Fink, D. Grove, "Space- and Time-Efficient Implementation of the Java
  Object Model", ECOOP 2002.
- JEP 450 and JEP 519, Compact Object Headers (OpenJDK); JDK-8354672.
- "Pointer Compression in V8", v8.dev, 2020.
- "Mixed Blocks: Storing More Fields Flat", OCaml Workshop 2024; "Layout Polymorphism",
  ML Workshop 2023; the OCaml unboxed-types RFC.
- A. Reinking, N. Xie, L. de Moura, D. Leijen, "Perceus", PLDI 2021; A. Lorenzen,
  D. Leijen, "Reference Counting with Frame Limited Reuse", ICFP 2022; A. Lorenzen,
  D. Leijen, W. Swierstra, "FP²: Fully in-Place Functional Programming", ICFP 2023;
  S. Ullrich, L. de Moura, "Counting Immutable Beans", IFL 2019.
- Lean Zulip, "Unboxed structure types" (Feb 2024).
