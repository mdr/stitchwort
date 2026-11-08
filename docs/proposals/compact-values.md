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

## 7. Not done, and findings

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
