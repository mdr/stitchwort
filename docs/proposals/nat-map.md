# Proposal: a map keyed by natural numbers (Haskell's `IntMap`)?

**Status:** draft 1, 7 November 2026. Ticket SW-1603 (from SW-1473), design work Matt asked
for on 7 Nov. Nothing is built, and nothing was built or run for this note: other lanes
were compiling. Where a number matters and isn't already in the repository, §7 says how to
measure it and what result would change the recommendation. The note stops for Matt's
decisions ([§8](#8-decisions), D2595–D2601). Written against `main` at `5062bde53`.

Labels, as in the other notes:

- **[checked]**: read in this repository at the place given.
- **[measured earlier]**: a figure from a note or ticket in the repository, with where it
  came from. Nothing was run for this note.
- **[cited, not re-checked]**: from memory of the published source; not re-read for this
  note.
- **[inferred]**: my reasoning from checked facts.
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The need](#1-the-need)
2. [The options](#2-the-options)
3. [Keys](#3-keys)
4. [How it fits with the rest of Stitchwort](#4-how-it-fits-with-the-rest-of-stitchwort)
5. [How others do it](#5-how-others-do-it)
6. [Recommendation](#6-recommendation)
7. [Staged plan, and what to measure](#7-staged-plan-and-what-to-measure)
8. [Decisions](#8-decisions)

## 0. Summary

**The problem.** Std's `Map` is slow when a program runs: about 7 µs per insert with `Nat`
keys on `stitchwort run`, 15 µs with grid `Position` keys and 20 µs with `List Int` keys,
against well under 1 µs in Python. The question was whether a separate map for natural-number
keys, a Patricia trie like Haskell's `IntMap`, is the fix.

**What the evidence says.**

- **The dense cases are already solved.** Arrays (SW-1637–SW-1639) took 2020 day 15 from
  357 s to 16 s and day 11 from 23 s to 5.4 s. Those were the two programs that started
  this ticket.
- **The slow maps left are mostly not keyed by numbers.** In `aoc/`, the hot maps and sets
  are keyed by `Position` (a record of two `Nat`s), `Cube` (a `List Int`), `Changes` (four
  `Int`s) and `(Nat, Position)`. Maps keyed by `Nat` exist in eight files, and none of
  those programs is recorded as slow. A `Nat`-only map would help few real programs unless
  they encoded their positions as numbers, which works against D2363's domain records.
- **`Map` is slow mainly because of the interpreter, not comparisons.** An insert runs
  about 1,480 bytecode instructions and 81 calls. Two thirds of the time is the machine's
  dispatch loop, and the balancing code alone is about half the instructions. A `Nat`
  comparison is a small share, because the optimiser already copies `Map.insertWith` for a
  known `Nat.instOrd`. Comparisons do matter for structured keys: `List Int` keys cost
  three times what `Nat` keys do.
- **A trie written in Stitchwort buys little.** The arrays note measured one: 1.5× faster
  than `Map` on the machine, and *slower* under `--js` and `--native`. Std's bitwise `Nat`
  operations are also written in Stitchwort (4.3 µs per XOR), so a Patricia trie would
  first need native bit operations.

**The recommendation: no new map type now. Make `Map` itself fast, for every key whose
order is "structural".**

- Implement the few hot tree functions (`Map.Tree.get`, `Map.Tree.insertWith`, then the
  other walks) as trusted natives in Rust, bound by content hash like the `Text` and
  `Array` natives. They work on the same tree values and build exactly the same trees as
  the definitions. So nothing changes for the kernel, the proofs, the API, printing or
  hashing, and every existing `Map` and `Set` program gets faster with no edits.
- Use them where the key's order is one Rust can compute directly: `Nat`, `Int`, `Char`,
  `Text`, `Bool`, and derived `Ord` on records and data types built from those (which
  covers `Position`, `Cube`, `Changes` and pairs). Anything else runs the definitions as
  today.
- Expected: inserts from 7–20 µs to about 0.3–1 µs on the machine and under `--native`
  (which shares the machine's natives), so 10–30× on map-bound loops **[inferred]**.
- **Stage 0 is a measurement**, a profile of three map-heavy days and a micro-benchmark,
  with a go/no-go rule (§7). A `Nat`-keyed Patricia trie stays on the shelf with a named
  trigger: build it only if a measured program still needs it afterwards.

## 1. The need

### 1.1 What started this

- **2020 day 15** kept `lastSeen: Map Nat Nat` over 30 million turns: 357 s on
  `stitchwort run`, 127 s `--js`, 84 s `--native`, 7 s in Python **[measured earlier:
  `aoc/NOTES-2020.md` day 15, item 1]**. With `Array` it takes 16 s on the machine and 7 s
  native **[measured earlier: SW-1637, SW-1657]**.
- **2020 day 11** made eight `Map` lookups per seat per round: 19.3 s **[measured earlier:
  NOTES-2020 day 11]**. With `Grid.lookup` backed by arrays, 5.4 s **[measured earlier:
  SW-1637]**.

Both were *dense*: the keys were 0 to n−1. An array is the right structure for them and is
built. This ticket asks about the other case: *sparse* keys, numbers spread thinly over a
large range, where an array would be mostly empty.

### 1.2 Who uses maps keyed by numbers today

From `grep` over `aoc/src`, outside proofs **[checked]**:

| Key type | Where | Recorded run time |
|---|---|---|
| `Nat` | 2020 day 14 memory (`Map Nat Nat`, 80,123 36-bit addresses) | 1.8 s **[NOTES-2020]** |
| `Nat` | 2024 day 11 stone counts, 2025 day 8 circuit labels (1,000 entries), 2024 day 9 free space, 2024 day 6 sightlines (`Map Nat (Set Nat)`), `Aoc.Common.PrefixSums` (`Map Nat (Map Nat Nat)`) | none recorded as slow |
| `Position` (`{ row: Nat, column: Nat }`) | 2024 days 6, 8, 12, 16, 18, 20; 2021 day 15; many `Set Position` | 2021 day 15: 17.6 s, "most of it" `Map`/`Set` **[NOTES-2021 day 15]** |
| `Cube` (`{ coordinates: List Int }`) | 2020 day 17 | 8.4 s, 383,120 `insertWith`s at about 20 µs each **[NOTES-2020 day 17]** |
| `Changes` (four `Int`s) | 2024 day 22 | no real input; its time is dominated by `Nat.xor`, 4.3 µs each **[NOTES-2024 day 22]** |
| `Computer` (`Text`), `Reindeer`, `Guard`, `Cell` | 2024 days 23, 16, 6, 15 | — |

Counting declarations, `Set Computer`, `Set Position`, `Map Position`, `Set Cell` and
`Set Cube` together outnumber `Map Nat` and `Set Nat` about five to one. `PrefixSums` is
dense and should be an array anyway.

So a `Nat`-only map would speed up 2020 day 14 (already fast) and a few others not recorded
as slow. The slow programs would need their positions encoded as numbers first (§3.2).

### 1.3 Why `Map` is slow

Measured for the native-compilation note: a million `Set.fromList` inserts of `Nat`s take
8.7 s on the machine and 3.2 s under `--js` **[measured earlier:
`docs/proposals/native-compilation.md` §1.2]**. Per insert:

- **About 1,480 bytecode instructions in 81 calls**, at about 6 ns per instruction.
  `Map.Tree.shape` (choosing a rotation from subtree sizes, with multiplications) is about
  40 instructions per call, roughly half the total.
- **Where the time goes:** 63% in the machine's dispatch loop, 11% dropping values, 7%
  allocating, 4% growing the register vector. The rest is mostly the `Nat` primitives
  (`nat_add`, `nat_mul`), much of it in the size arithmetic.
- **Reuse is poor.** `insertWith` takes a node apart, but `balance` → `rebuild` → `bin`
  builds the new one in another function, so the cell can't be reused in place
  **[checked: `docs/research/in-place-reuse.md` §2.2]**.
- **Comparisons are already cheap for `Nat`.** The optimiser copies a recursive function
  called with a known dictionary (`Map.insertWith` at `Nat.instOrd`) and inlines the
  comparison **[checked: `crates/rt/src/opt.rs:21-28`]**. `Nat.compare` is two primitive
  calls, `Nat.equal` then `Nat.leq` **[checked: `std/core/Ordering.sw:16`]**.
- **Comparisons are not cheap for structured keys.** `Position` keys cost about 15 µs per
  insert against 7 µs for `Nat`, and `List Int` keys about 20 µs **[measured earlier:
  NOTES-2021 day 15; NOTES-2020 day 17]**. A derived `compare` goes field by field through
  each field's dictionary and builds an `Ordering` value at each step.

Under `--js` every `Nat` is a `bigint`, and every tree node and `Ordering` is an object
**[measured earlier: NOTES-2020 day 15]**. Under `--native` the compiled code is faster
per instruction but does the same work.

**So:** for `Nat` keys, `Map` is slow because of the interpreter's cost per instruction and
the amount of balancing work per level, not because of comparisons. For structured keys,
comparisons roughly double or treble that. A specialised `Nat` comparison would gain little,
since it mostly exists already.

### 1.4 What a Patricia trie would and wouldn't fix

A big-endian Patricia trie (Okasaki and Gill, 1998) branches on bits of the key. It never
compares keys for order, never rebalances, and its depth is at most the key's bit length
(and about log₂ n for spread-out keys). Unions and intersections work on whole subtrees,
so merging two tries with disjoint ranges is nearly free **[cited, not re-checked]**.

Per level, a trie insert does a mask-and-compare on the prefix, one bit test and one new
node. In Stitchwort that would be perhaps 15–25 instructions a level, against Map's ~70,
if the bit operations were single primitives **[inferred]**. They aren't:

- `Nat.and`, `Nat.xor`, `Nat.shiftRight` and `Nat.testBit` are written in Stitchwort, by
  repeated halving **[checked: `std/Nat/Bits.sw:22-60`]**. One XOR of a 24-bit number took
  4.3 µs **[measured earlier: NOTES-2024 day 22]**. Native versions are an open item on
  SW-808.
- The one trie that was tried (a 25-level binary trie keyed by the number's bits, for the
  arrays note) ran day 15 at 8.4 µs a turn against `Map`'s 12.3 µs on the machine: 1.5×.
  Under `--js` and `--native` it was *slower* than `Map` **[measured earlier:
  `docs/proposals/arrays.md` §3.2 U4, §7]**.

So a trie written in Stitchwort, even with native bit operations, would be about 2–4×
faster than `Map` on the machine for `Nat` keys **[inferred]**, would help `--js` little
(bit operations on `bigint`s allocate), and would not help the slow programs at all, since
their keys aren't numbers.

## 2. The options

### (a) A std `NatMap` written in Stitchwort, as a Patricia trie

- **API.** The same names as `Map` (`empty`, `singleton`, `insert`, `insertWith`, `get`,
  `getOr`, `contains`, `remove`, `alter`, `adjust`, `map`, `filter`, `filterMap`,
  `foldLeft`, `foldRight`, `toList`, `fromList`, `union`, `unionWith`, `intersectWith`,
  `difference`, `min`, `max`, `below`, `above`, `size`, `keys`, `values`), with `NatSet`
  beside it, so code switches by changing the type. `size` is O(n) unless the nodes store
  sizes.
- **Proofs.** A Patricia trie is unique for its contents, so it needs no quotient: two
  well-formed tries with the same entries are the same trie. But that has to be proved
  (the well-formedness invariant: each branch's prefix and mask agree with every key below
  it, and no branch is empty), and then every operation needs a lemma relating it to the
  sorted entry list, as `std/Map/Spec.sw` does for the tree. Map's proofs are about 4,100
  lines across `Raw.sw`, `Spec.sw` and `Map.sw` **[checked: `wc -l`]**; a trie's would be
  comparable, perhaps less, since there is no balancing **[inferred]**.
- **Run time.** Machine 2–4× faster than `Map` for `Nat` keys, once SW-808's native bit
  operations exist; JS about the same as `Map`; native a little better **[inferred from
  §1.4]**.
- **Maintenance.** A second container family in std with its own invariants, its own
  lemmas and its own bugs, used by a handful of programs.

### (b) A native-backed `NatMap` with a pure model

Following `Array`'s design (D2459): proofs see a record around an existing type, and the
runtime keeps something faster.

- **Model.** `type NatMap v = { toMap: Map Nat v }`, every operation defined on `toMap`.
  Then every `Map` lemma applies through `.toMap` with no new proofs, `DecEq` and `==` come
  from `Map`'s (map-equality.md's quotient), and `NatMap.ext` is one line from `Map.ext`.
  This is much cheaper in proofs than (a).
- **Run time.** A new `Value` variant holding a Rust ordered map from `u64` to `Value`
  (with `BigNat` keys falling back to the definition), and about 20 natives bound by hash,
  all or nothing, as for `Array`. Updates in place when unshared, as `Array.set` does.
  When shared, either copy (Array's cliff, but for a map an O(n) copy is a bad surprise in
  ordinary persistent code: a breadth-first search that keeps old `seen` sets) or use a
  persistent structure (a Rust HAMT or B-tree with shared nodes). Each operation would be
  a native call of about 0.04 µs plus the Rust map's own cost, so perhaps 0.1–0.5 µs
  against 7 µs **[inferred; the 0.04 µs is from arrays.md §7]**.
- **JS.** A version map (Baker's trick again: the newest version holds a JS `Map`, older
  ones hold the change back to it), sorting the keys when an ordered operation (`toList`,
  `min`, `below`) needs them. `bigint` keys in a JS `Map` compare by value **[unverified]**.
- **Bridges.** Code that reads `.toMap` pays an O(n) conversion, as with `Array.toList`.
  So every operation in the API must be native, or a missed one silently costs O(n).
- **Maintenance.** A new value kind in the runtime, the native-code layout probe, the JS
  backend and the boundary codecs; the binding test. Moderate, and the same work as
  `Array`, but for `Nat` keys only, which (§1.2) aren't where the slow programs are.

### (c) Make `Map` itself fast, through native tree walks

Instead of a new type, give the hot functions of `Map.Tree` native implementations that
work on the *same* tree values.

- **What it is.** `Map.Tree.get`, `Map.Tree.insertWith` and, later, the other walks
  (`remove`, `alter`, `adjust`, `min`/`max`, `nearestBelow`/`nearestAbove`, `fromSorted`,
  `toListOnto`) written in Rust over `Value::Data` nodes, following the Stitchwort
  definitions step for step: same rotations, same stored sizes, so the same trees.
  Persistence comes for free: a new path of nodes, sharing the untouched subtrees, as now.
  Reusing a node in place when its count is 1 is a later option.
- **When they apply.** Only when the key's order is *structural*: one Rust can compute from
  the values alone. That is the base instances (`Nat`, `Int`, `Char`, `Text`, `Bool`,
  `Ordering`) and derived `Ord` over fields whose orders are structural, plus
  `Pair.instOrd`, `List.instOrd` and `Option.instOrd` at structural arguments. Derived
  `compare` is "constructor index first, then the fields left to right" **[checked:
  `crates/elab/src/derive_ord.rs:26-47`]**, and `List.compareLex` is the same order with
  `[]` first **[checked: `std/core/CompareData.sw:10-14`]**. A Rust function comparing
  values by tag and then fields gives that order, provided the runtime's constructor
  numbers are declaration order (to check; `Value::Tag` and `Value::Data` both carry a
  `u32` **[checked: `crates/rt/src/value.rs:45-48`]**). `Float` and hand-written instances
  are left out at first. Everything else, including `[ord := descending]`, runs the
  definitions as today.
- **How the runtime knows.** At compile time, where the optimiser already sees a known
  dictionary (it copies `Map.insertWith` for one): if the dictionary is structural, call
  the native. Derived instances get a flag from `derive_ord` saying they are structural.
  Where the dictionary is only known at run time, the definition runs. A fallback by
  pointer identity on a registered set of dictionaries is possible later.
- **API, proofs, equality.** Unchanged. There is no new type and no new lemma; the kernel
  and the checker never see the natives (DESIGN.md §13). `Map`'s quotient, `Map.ext`,
  `DecEq` and `Ord` stay as built.
- **Run time.**
  - *Machine and `--native`*: one native call per operation, then about 20 levels of
    tag-and-field compares and node building in Rust. Perhaps 0.3–1 µs per insert and
    0.1–0.3 µs per lookup, against 7–20 µs and 2–5 µs, so **10–30×** on map-bound loops,
    more for structured keys **[inferred]**. `--native` calls the machine's natives
    **[checked: arrays.md §4.2]**, so it gets the same.
  - *JS*: hand-written JS versions of the same walks, over the generated objects, with a
    structural compare on `bigint`s, strings and objects. They would remove the dictionary
    calls and the `Ordering` objects but not the `bigint`s. Perhaps 2–3× **[inferred]**.
    A later stage, after the machine's numbers.
  - *`run --reference` and the kernel*: unchanged, the definitions.
  - *Memory*: unchanged. A node is still a `Value::Data` with five fields.
- **Trust.** The natives are trusted at run time, as the `Text` and `Array` ones are.
  Because they build the same trees, a differential test can compare whole trees, not
  only answers: random operation sequences on `Nat`, `Position` and `List Int` keys, run
  once through the natives and once through the definitions.
- **Maintenance.** About eight Rust functions now and the same in JS later, which must
  change whenever `Map.Tree`'s algorithm does. Hash binding catches drift: a changed
  definition stops binding. A lost binding costs a constant factor, not an asymptotic one,
  so it can fall back quietly as `Text`'s do, but SW-1582 shows a quiet loss goes unseen,
  so the binding test runs in the fast `std` lane (§4.5).
- **What it doesn't fix.** The balancing work itself (rotations, sizes) is still done, in
  Rust instead of bytecode; and maps with non-structural orders stay slow. Memory per entry
  stays high (about 190 bytes at day 15's scale **[inferred from 688 MB for 3.6M keys]**).

### (d) Nothing new: arrays and `Map` as they are

- Dense keys use `Array`, which is built. Sparse keys use `Map`, at today's speed.
- Smaller improvements to `Map` still apply: a fused `balanceL`/`balanceR` as in
  `Data.Map` (SW-814, about 30% fewer instructions a level, but it means re-proving
  `balanceWithin`, `balanceSized` and `balanceOnto`), and building nodes where the reuse
  pass can claim the old cell (in-place-reuse.md §2.2). These help every backend,
  including JS, by perhaps 1.3–1.5× **[inferred]**.
- The general interpreter work (SW-813, about 6.5 ns per instruction) speeds up `Map` along
  with everything else.

### Side by side

| | (a) trie in std | (b) native `NatMap` | (c) native `Map` walks | (d) nothing |
|---|---|---|---|---|
| Programs helped | `Nat` keys | `Nat` keys | every structural key: `Nat`, `Position`, `Cube`, `Text`, pairs | — |
| Code changes for users | change the type | change the type | none | none |
| Machine / native speed-up | 2–4× (after SW-808) | 15–50× | 10–30× | 1.3–1.5× (SW-814) |
| JS speed-up | ~1× | 3–10× (version map) | 2–3× (later stage) | 1.3× |
| New proofs | ~2,000+ lines | a few one-liners | none | re-prove balance (SW-814) |
| New runtime pieces | none (SW-808's bit natives) | a value kind, ~20 natives, JS version maps, codecs | ~8 natives over existing values, a structural compare, a flag on derived `Ord` | none |
| Risk | a second container's bugs | sharing cliff, bridges | natives drifting from definitions | — |

All speed-ups are estimates **[inferred]** until §7's measurements.

## 3. Keys

### 3.1 `Nat` only, or `Int` too?

For (c) the question disappears: every structural key works, `Int` included, and the order
is the key's own `Ord`.

For a trie, should one ever be built (stage 3): `Nat` first. `Int` keys can be mapped to
`Nat` with the order kept (for example `2n` for n ≥ 0 and `2(−n)−1` for n < 0 keeps the
keys distinct but not in order; a sign-split root, as Haskell's `IntMap` does to keep
`toList` in signed order, is the usual answer) **[cited, not re-checked]**. That is a
detail for the stage that needs it.

### 3.2 Grid positions encoded as numbers?

A position `{ row, column }` could be a `Nat` key, `row * width + column`, or a pairing
function for unbounded grids. This is what an `IntMap` user would do. It conflicts with
D2363: positions are records with methods, and specs and proofs are stated about them.
An encoding also changes the order (a pairing function is not row-major), so `toList` and
`min` would mean something else, and proofs would carry the encoding's injectivity around.

Under (c) none of that is needed: `Position` with derived `Ord` is structural, so
`Set Position` gets the native walks as it stands. That is the main reason (c) beats (a)
and (b) here.

## 4. How it fits with the rest of Stitchwort

### 4.1 Derived `Ord` on records

- (c) needs `derive_ord` to record that an instance is structural (every field's order is
  structural, no hand-written `compare` in the chain). The optimiser reads the flag where
  it already recognises known dictionaries (`opt.rs`; JS's `known_compare`,
  `crates/js/src/lib.rs:4271-4300` **[checked]**).
- A type with a hand-written `Ord` instance just runs the definitions.
- (a) and (b) need nothing here, but their keys are `Nat` only.

### 4.2 `Map` and `Set` conversions, `for` and folds

- (c): nothing changes. `.toMap`, `.toSet`, `Map.counts`, `groupBy`, `for` over a map,
  `foldLeft` and `foldRight` are the same functions. `Set` is a record around `Map k ()`
  **[checked: map-equality.md §14.1, step 2.1]**, so it speeds up with `Map`.
- (a) or (b) would need `List.toNatMap`/`.toNatSet`, conversions to and from `Map`, and the
  folding functions repeated, and the guide would have to explain when to pick which.

### 4.3 Printing

- (c): unchanged. `Show` prints `Map.fromList [...]` in key order.
- (a)/(b): `NatMap.fromList [...]`, in key order.

### 4.4 Equality

- (c): unchanged. `Map` is the quotient of trees by "same entries", with `DecEq`, `Ord` and
  `Map.ext` **[checked: map-equality.md §14.1]**.
- (b): inherited from `Map` through the `toMap` field; derived `==` on a record with a
  `NatMap` field works with no deriving change.
- (a): a canonical trie gives `=` directly, after the uniqueness proof.

### 4.5 The check cache, hashing and binding

- **Hashes.** Content hashes are of declarations, and a run-time map value is never hashed
  **[checked: arrays.md §4.5]**. (c) adds no std declarations (only the derived-instance
  flag, which is recomputed, not hashed, as D921's flags are), so no snapshot changes. (a)
  and (b) add std declarations; their brief would ask for `snap:hashes` and the
  `hash_stability` test.
- **The check cache** keys on declaration hashes and the binary's fingerprint, so a new or
  changed native invalidates as any compiler change does **[checked: arrays.md §4.5]**.
- **Binding.** Natives are bound to `Map.Tree.get` and the rest by content hash. A std edit
  that changes one of those definitions unbinds its native. The extract crate's
  `bound_to_the_prelude` tests (and a new one per Map native) catch that in the `std` lane.
  Since a lost Map native costs a constant factor, falling back quietly is acceptable;
  `Array`'s all-or-nothing `E-BUILTIN` rule was for natives whose loss is asymptotic
  (D2463).

### 4.6 The reference evaluator and the playground

- `run --reference` runs the definitions, so it stays the oracle for the differential test.
- The playground runs the machine compiled to WebAssembly, so it gets (c)'s natives with the
  machine.

## 5. How others do it

All **[cited, not re-checked]**; from memory of the libraries' documentation and papers.

- **Haskell `containers`.** `Data.Map` is the weight-balanced tree Stitchwort's `Map`
  copies (Adams; delta 3, ratio 2). `Data.IntMap` is a big-endian Patricia trie on machine
  `Int`s (Okasaki and Gill, "Fast Mergeable Integer Maps", 1998), with depth at most the word
  size, and the sign bit handled at the root so `toList` is in signed order. `Data.IntSet`
  packs 64 keys into a bitmap at each leaf. `IntMap` is typically 1.5–3× faster than
  `Map Int` for lookups and inserts and much faster for unions. All of this is compiled
  code with single-instruction bit operations.
- **Lean 4.** `Std.TreeMap` (size-balanced, like `Data.Map`) and `Lean.RBMap` (red-black),
  `Std.HashMap` (an array of buckets, updated in place when unshared). Proofs go through
  the extensional versions (`ExtTreeMap`, `ExtHashMap`, quotients), as Stitchwort's `Map`
  does. There is no `IntMap`. Speed comes from the compiler (reference counting and in-place
  reuse in compiled C), not from natives for the containers.
- **OCaml.** `Stdlib.Map` is an AVL tree over a comparison functor; `Hashtbl` is mutable.
  Patricia-tree integer maps live in libraries (Filliâtre's `ptmap`), not the standard
  library.
- **Koka.** Containers are ordinary Koka code; its speed comes from Perceus reference
  counting and "functional but in-place" reuse, which makes a red-black tree insert update
  in place when unshared.
- **Roc.** `Dict` is a hash map written in Roc over `List`, mutated in place when the
  reference count is one. There is no ordered map or integer map among the builtins.

What this shows: the languages that make maps fast do it either by making generic tree
code fast (Lean and Koka: compilation, in-place reuse) or with a built-in structure updated
in place when unshared (Lean's `HashMap`, Roc's `Dict`). An integer trie is a niche
structure, worth it in Haskell for fast unions and lower constants in compiled code. (c)
is the nearest Stitchwort can get to the first route today, for the functions that matter,
without waiting for a compiler.

## 6. Recommendation

1. **No `NatMap` type now** (option (d) for the type question). The programs that started
   this are solved by arrays, and the slow maps that remain are keyed by records.
2. **Make `Map` fast for structural keys with native tree walks** (option (c)), after a
   measurement confirms the time is in `Map` (stage 0). It speeds up every existing `Map`
   and `Set` program with a structural key, including `Set Position`, without changing a
   line of user code or a proof.
3. **Keep the Patricia trie as a conditional later stage**, behind a named trigger (§7,
   stage 3). If it is ever built, build it as (b), a native with `Map Nat v` as its model,
   not as (a): (b)'s proofs are nearly free, and (a)'s speed-up is too small for its proof
   cost.
4. **SW-808's native `Nat` bit operations** are worth doing on their own (2024 day 22,
   2020 day 14, `Random`), and are a prerequisite for any trie. They are independent of
   this note.

## 7. Staged plan, and what to measure

### Stage 0: measure (a lane, no code changes; about 45 min)

**Benchmarks** (scratch programs, not committed):

- **B1, micro, `Nat` keys.** Insert 10⁶ keys `k = i * 7919 % 1000003` (spread out, not
  ascending) into a `Map Nat Nat`, then sum `getOr k 0` over the same keys. Report µs per
  insert and per lookup, each timed by subtracting the same program at 1 key.
- **B2, the same with `Position` keys** `{ row = k / 1000, column = k % 1000 }`, and **B3**
  with `List Int` keys of length 3 (day 17's shape).
- **Days on their real inputs:** 2020 day 17 (8.4 s; `Set Cube`), 2021 day 15 (17.6 s;
  `Map Position Nat`, `Set (Nat, Position)`), and 2020 day 14 (1.8 s; the one sparse
  `Map Nat Nat` with a real input).
- Each on `stitchwort run`, `--js` and `--native`, user seconds, plus
  `stitchwort run --profile FILE --profile-top 40` on the machine
  **[checked: `docs/proposals/run-profiler.md`]**.

**What to report:** for each day, the share of profile samples under `Std.Map.Tree.*`,
`Std.Map.Raw.*` and the key's `compare` (derived `compare`, `List.compareLex`,
`Nat.compare`), and the split between the walk and the comparison.

**The go/no-go rule:**

- **Go to stage 1** if `Map`/`Set` (tree functions plus key comparisons) are at least 50% of
  the samples on at least two of the three days.
- **Stop, and put the effort into SW-813 (interpreter speed) instead**, if they are under
  30% on all three: then the maps aren't the problem.
- **What would change the recommendation towards a trie:** B1's lookups being much faster
  than its inserts (so balancing dominates), *and* a real program with `Nat` keys that is
  slow. Neither is known today.

### Stage 1: native `get` and `insertWith` on the machine (Opus; runtime and optimiser)

- A structural compare in Rust over `Value` (numbers by value across `Nat`/`BigNat` and
  `Int`/`BigInt`, `Text` by code point, constructors by tag then fields), with a test that
  it agrees with each base instance's `compare` and with derived `compare` on random values.
- A "structural" flag on derived `Ord` instances, and its rules for `Pair`, `List` and
  `Option`.
- Natives for `Map.Tree.get` and `Map.Tree.insertWith`, bound by hash, chosen by the
  optimiser at a known structural dictionary; the definitions otherwise. Building exactly
  the definitions' trees.
- A differential test: random sequences of inserts and lookups on B1–B3's key types,
  comparing whole trees between the natives and the definitions. The binding test in the
  `std` lane.
- **Success number:** B1 inserts at ≤ 1 µs (from about 7–9) and lookups at ≤ 0.3 µs on the
  machine; 2020 day 17 at ≤ 3 s (from 8.4); 2021 day 15 at ≤ 8 s (from 17.6). Same answers
  everywhere.
- **Brief notes for the orchestrator:** native-binding brief rules apply (memory note
  "Native hash pins"): run extract's `bound_to_the_prelude` tests. No std declaration
  changes, so no `snap:hashes`.

### Stage 2: the other walks, then JS (Sonnet for the walks; Opus for JS if it gets tricky)

- `remove`, `alter`, `adjust`, `min`/`max`, `nearestBelow`/`nearestAbove`, `fromSorted`,
  `toListOnto`, each with its differential test.
- JS versions of `get` and `insertWith`, measured on B1–B3 `--js` before the rest.
  Success: B1 `--js` at ≤ half today's time.
- Optional: reuse a node in place when its count is 1, measured on B1 (in-place-reuse.md's
  plan, D2273–D2277).

### Stage 3 (only if triggered): a `Nat`-keyed trie

**Trigger:** after stage 2, a real program keyed by sparse `Nat`s (or one that can't avoid
`Nat` keys) still spends over half its time in `Map`, or a `Nat`-keyed map is too big for
memory at about 190 bytes an entry. Then: option (b), `NatMap v = { toMap: Map Nat v }`
with a native persistent trie or B-tree behind it, its own design brief, and SW-808's bit
operations if it is written in Stitchwort.

### Tickets to file

1. **Stage 0: profile `Map` on 2020 day 17, 2021 day 15 and 2020 day 14, plus B1–B3**
   (performance epic; no build of std changes; Sonnet; expected 45 min). Needs a release
   build, so not during a heavy compile.
2. **Stage 1: native `Map.Tree.get`/`insertWith` for structural key orders** (performance;
   Opus; expected 180 min; after 1, if it says go).
3. **Stage 2a: the other `Map.Tree` walks as natives** (performance; Sonnet; 90 min; after 2).
4. **Stage 2b: JS versions of the `Map` walks** (performance; Sonnet; 90 min; after 2).
5. **Backlog, stage 3: a `Nat`-keyed trie, with the trigger above** (performance; design).
6. Update **SW-814** (fused balance): lower priority once stage 1 lands, since the machine
   then no longer runs the balance code; still useful for JS and for non-structural keys.
7. **SW-808**'s native bit operations: already filed; unblock it as its own work.

SW-1603 itself can close with this note, once the decisions are recorded.

## 8. Decisions

Each with a recommendation.

- **D2595. A `NatMap` type now?** (a) a trie in Stitchwort / (b) a native-backed `NatMap`
  over `Map Nat v` / (c) no new type; speed up `Map` itself / (d) nothing at all.
  **[rec: (c).** Arrays already cover the dense cases; the slow maps left are keyed by
  records, which a `Nat` map can help only through encodings that work against D2363.**]**
- **D2596. Stage 0 first:** a measurement lane with the go/no-go rule in §7, before any
  runtime code. **[rec: yes.** The 50% figure is the difference between this work and
  SW-813's, and it costs 45 minutes.**]**
- **D2597. How `Map` gets faster:** native walks over the existing tree values, building the
  same trees as the definitions / a new native value kind for maps (a Rust B-tree or HAMT)
  with the tree as its model. **[rec: walks over the existing values.** No bridges, no
  sharing cliff, no change to memory or the codecs, and the differential test can compare
  whole trees.**]**
- **D2598. Which key orders use the natives:** the base instances plus derived `Ord` over
  them, with `Pair`, `List` and `Option` at structural arguments; `Float` and hand-written
  instances run the definitions. **[rec: yes, as stated.** It covers every hot key in
  `aoc/`.**]**
- **D2599. A lost binding:** fall back to the definitions quietly, with a binding test per
  native in the `std` lane / refuse the program with `E-BUILTIN` as for `Array`.
  **[rec: quiet fallback plus the test.** The loss is a constant factor, as for `Text`; an
  error for a std edit that only slows `Map` would be out of proportion.**]**
- **D2600. JS:** native JS walks in stage 2, after the machine's numbers / leave `--js` running
  the definitions. **[rec: stage 2, measured on `get` and `insertWith` first.** JS is already
  about 3× faster than the machine on maps, so its gain is smaller and can wait.**]**
- **D2601. The trie:** keep it as a conditional stage 3 with §7's trigger, as option (b) if
  ever built, and close SW-1603 with this note. **[rec: yes.]**
