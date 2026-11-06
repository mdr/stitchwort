# Proposal: an array in std

**Status:** draft 1, 6 November 2026. Ticket SW-1473, for Matt's D2450 ("do a full design
note with Opus, thoroughly search both the literature for this and how other functional
languages, Lean, Haskell, Rocq, Idris, Agda etc."). Nothing is built; this note stops for
Matt's decisions ([§9](#9-decisions), Q1–Q10). Written against `main` at `750f3222`.

It takes over two earlier threads, and agrees with both:

- **SW-112** (19 Oct), "Array type with get/set/length", which is still in the backlog. It
  asked for this note, then was put off when 2025's day 4 turned out not to need an array
  (D427).
- **[docs/research/compilation.md](../research/compilation.md) §5.1** and its D1920
  ("write the design note around a list-specified `Array` with in-place update on unique
  values … build only after it settles the JS choice"). That section's sketch is §4 here,
  with the JS choice settled in §4.3.

It also builds on [docs/research/in-place-reuse.md](../research/in-place-reuse.md) (SW-1159,
D2273–D2277 still open). §5 says how the two relate.

Labels, as in the other notes:

- **[checked]**: read in this repository at the place given.
- **[ran]**: run for this note on 6 Nov 2026 on the Apple M4 Pro, with the release CLI
  built from `750f3222`, Node 22.23.3 and Python 3.14.7. The daily tier was running, so
  times are rough. They are single runs, user CPU seconds unless marked. The scratch
  programs are not in the repository; §7 lists them.
- **[cited]**: read in the source linked, on 6 Nov 2026.
- **[inferred]**: my reasoning from checked or cited facts.
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Prior art](#2-prior-art)
3. [The options](#3-the-options)
4. [Recommendation](#4-recommendation)
5. [How this relates to the in-place reuse plan](#5-how-this-relates-to-the-in-place-reuse-plan)
6. [Risks](#6-risks)
7. [Measurements](#7-measurements)
8. [Staged plan, and the evidence still to collect](#8-staged-plan-and-the-evidence-still-to-collect)
9. [Decisions](#9-decisions)
10. [Sources](#10-sources)

## 0. Summary

**The problem.** Std has no array: no sequence where reading or changing the element at a
position takes constant time. Programs that keep state by position use `Map`, a balanced
tree, and on big inputs the tree is nearly all the cost.

- 2020 day 15 part 2 plays 30 million turns. Each turn reads and writes one entry. It takes
  **357 s** on `stitchwort run`, 127 s under `--js` and 84 s under `--native`. Python, with
  a `dict`, takes 7 s.
- 2020 day 11's grid simulation spends most of its 19 s on `Map` lookups, eight per seat
  per round.

**The recommendation**, which is Lean 4's design fitted to Stitchwort:

- **What proofs see.** `Array a` is an ordinary std record around a list, and every
  operation is an ordinary definition on that list. The kernel is unchanged, and there is
  no new axiom. The proofs are list proofs: `getSet`, `getSetOther`, `sizeSet` and `ext`
  are a line or two each over the existing `List.get`/`List.set` lemmas.
- **How it runs.** On the machine, native code and the playground, an array is one buffer
  of values. Its operations are natives bound to their definitions by content hash, the way
  `Text`'s are. A `set` on an array nothing else refers to changes it in place: the
  runtime already counts references and moves values on their last use. A `set` on a shared
  array copies it first, which is always correct but O(n).
- **In JS**, where there are no reference counts, an array is a version array (Baker's
  trick, also used by Rocq's kernel). The newest version owns the buffer, and each older
  version records the one change that tells it apart. A program that uses each version once
  gets O(1) updates. One that goes back to an old version still gets the right answer, and
  pays only for the steps back.
- **Guarding the speed.** Two changes in how natives bind, so an array can't silently fall
  back to O(n). Its natives bind all or nothing, and a mismatch is a loud error rather than
  a quiet fallback; SW-1582 is the reason. A counter reports copies made because an array
  was shared.
- **Not recommended:** a primitive, axiom-specified type in the kernel (Rocq's
  `PArray`: 11 axioms, and five critical bugs since 2020); a pure tree in std; a scoped
  mutable array behind an ability.

**Expected gain** **[inferred from §7's measurements; to be confirmed by stage 2]:** day 15
part 2 goes from 357 s to about 8–20 s on the machine, from 84 s to about 2–5 s native, and
from 127 s to about 10–25 s under `--js`. Python is at 7 s. Day 11 goes from 19 s to a few
seconds. Both days keep their proofs, apart from restating the invariant over the array
(day 15) or re-proving one shared lemma (`Grid.lookup`, for day 11 and 14 other days).

**Effort:** about 5–6 lane-days in four stages (§8). Each stage can stop, and stages 1
and 2 merge together.

## 1. The problem

### 1.1 What std has today

- **`List`** reads position i in O(i) (`List.get`, `List.getOr`), and `List.set` rebuilds
  the prefix up to i **[checked: `std/List/Toolkit.sw:171-186`]**.
- **`Vec a n`** is a list with its length in the type, also O(i) to index
  **[checked: `std/Vec/Vec.sw:11-14`, `:123`]**.
- **`Map k v`** is a weight-balanced tree inside a quotient, with O(log n) comparisons per
  `get` and `insert` **[checked: `std/Map/Map.sw:1-13`]**. `Map.byPosition` turns a list
  into a map keyed by position, which is how grid code indexes today
  **[checked: `std/Map/ByPosition.sw`; `aoc/src/Aoc/Common/Grid.sw:203-213`]**.

So a program that needs "the value at position i", changed once per step, has two choices:
a list, at O(n) a step, or a map, at about 20 comparisons, a fresh path of nodes and a
rebalance a step.

### 1.2 Day 15: 30 million turns of a map

The game keeps `lastSeen: Map Nat Nat`, the turn each number was last spoken. Each turn is
one `get` and one `insert` **[checked: `aoc/src/Aoc/Year2020/Day15/Day15.sw:33-49`]**.
Part 2 is 30,000,000 turns, with 3,611,894 distinct numbers, the largest 29,469,422. The
day's notes measured **[checked: `aoc/NOTES-2020.md`, day 15, item 1]**:

| runtime | time (user) | per million turns | peak memory |
| --- | --- | --- | --- |
| `stitchwort run` | 357 s | 11.9 s | 688 MB |
| `run --js` | 127 s | 4.2 s | 2.2 GB |
| `run --native` | 84 s | 2.8 s | 726 MB |
| Python, a `dict` | 7.2 s | 0.24 s | |

"The time is all the map": the same loop without it takes 0.1 s per million turns. The
numbers are all below the turn count, so the natural structure is a dense array from number
to turn. The notes add that old versions are never read again. So this day needs an array
that is *updated in place*, not merely a persistent one.

### 1.3 Day 11: a map walk for each neighbour

A round of part 1 made 72,000 `Grid.lookup` calls, eight per seat. Each was two
`Map.getOr`s, row then column, about 1.7 µs together. That was 0.12 s of a 0.21 s round,
and after other fixes the lookups are nearly all of it. `main` takes 19.3 s on the default
runtime, 4.1 s under `--js` and 3.7 s native
**[checked: `aoc/NOTES-2020.md`, day 11, item 1]**.

`Grid.lookup` lives in `Aoc.Common`. It builds a table of maps once and returns a lookup
function, and one lemma, `lookupAt`, ties it to `grid.at`
**[checked: `aoc/src/Aoc/Common/Grid.sw:203`; `aoc/src/Aoc/Common/Proofs/GridCells.sw:213`]**.
Fifteen files in `aoc/src` call `.lookup`. Backing that one function with an array would
speed all of them up without touching their proofs **[inferred]**.

### 1.4 What a newcomer sees

Both days are what a newcomer writes first: day 15 is Matt's own Scala, line for line. The
program is correct and proved, and it waits six minutes with nothing to say where the time
went. The 2024 day 4 notes said the same of grids: "every newcomer's first grid program will
look like `MapGrid`" **[checked: `docs/research/compilation.md` §5.1]**.

## 2. Prior art

There are two families of answers. One is a data structure in the library that is fast
without help from the runtime. The other is an array whose update is made safe by the type
system, by the runtime, or by the kernel. For each system below: what the logic sees, how
it runs, how the two are tied together, and what happens on a shared update.

### 2.1 The literature

**Version arrays (Baker's shallow binding).**
- The newest version is a real mutable array. Each older version is a node,
  `Diff(i, v, next)`: "I am `next` with position i holding v".
- Reading or updating an old version first *reroots*: it reverses the chain of `Diff`s so
  that this version owns the buffer.
- Single-threaded use costs O(1) per read and update. Going back to an old version costs
  the length of the chain, once.
- Sources: Baker, "Shallow binding in Lisp 1.5" (CACM 1978), which introduces rerooting for
  environments, and "Shallow binding makes functional arrays fast" (SIGPLAN Notices 1991)
  **[cited]**.
- GHC's old `Data.Array.Diff` was this. It warned that "accessing elements of older
  versions gradually becomes slower" **[cited]**.

**Conchon and Filliâtre** turned it into the standard modern form.
- "A Persistent Union-Find Data Structure" (ML Workshop 2007) builds union-find on Baker
  arrays and gives a Coq proof of `get`/`set` and of persistence against a model heap.
  That proof leaves `reroot` unverified, as an optimisation.
- "Semi-persistent Data Structures" (ESOP 2008) allows only going *back*, which is cheaper
  **[cited]**.
- Allain, Clément, Moine and Scherer, "Snapshottable Stores" (ICFP 2024), prove a
  generalisation of Baker's structure, rerooting included, in Iris/Coq **[cited]**.

**Purely functional trees with array-like interfaces.** These are plain inductive types, so
they're easy to reason about. None has O(1) access.
- Okasaki's skew binary random-access lists (FPCA 1995) and Braun trees ("Three
  algorithms on Braun trees", JFP 1997): O(log n) lookup and update **[cited]**.
- Finger trees (Hinze and Paterson, JFP 2006): O(log n) indexing **[cited]**.
- Bagwell's hash array mapped tries ("Ideal Hash Trees", 2001), Clojure's 32-way vectors,
  and RRB vectors (Bagwell and Rompf 2011; Stucki et al., ICFP 2015): O(log₃₂ n), copying
  one path per update **[cited]**.
- Patricia tries for integer keys (Okasaki and Gill, "Fast Mergeable Integer Maps", 1998),
  which Haskell's `IntMap` uses: O(min(n, word size)) **[cited]**.

**Types that allow in-place update.**
- Wadler, "Linear types can change the world!" (1990): a value that can't be copied or
  discarded can be updated destructively.
- Clean's uniqueness types (Barendsen and Smetsers, MSCS 1996): only arrays of unique type
  `*{a}` are updated, always destructively.
- Futhark (Henriksen et al., PLDI 2017): `a with [i] = v` consumes `a`, and the compiler
  checks that `a` is not used afterwards.
- Linear Haskell (Bernardy et al., POPL 2018): linearity on function arrows.
- Quantitative type theory (McBride 2016; Atkey, LICS 2018), as used by Idris 2 (Brady,
  ECOOP 2021, §4.1): a linear array is introduced through a continuation,
  `newArray : Int → (1 k : (1 arr : Array t) → a) → a`.
- Most recently, OCaml's modes (Lorenzen et al., "Oxidizing OCaml", ICFP 2024) give
  uniqueness under a garbage collector **[cited]**.
- All of these need a type-system feature that Stitchwort doesn't have, and they *reject*
  a shared use rather than copying it.

**In-place update by reference counting.**
- Ullrich and de Moura, "Counting Immutable Beans" (IFL 2019), used by Lean 4: with exact
  counts, an update on a value whose count is 1 can be destructive.
- Reinking, Xie, de Moura and Leijen, "Perceus" (PLDI 2021), used by Koka. It inserts
  counts precisely and reuses memory, which it calls "functional but in place".
- Lorenzen and Leijen, frame-limited reuse (ICFP 2022), and Lorenzen, Leijen and
  Swierstra, FP² (ICFP 2023).
- Roc's builtins do the same for its array-backed `List`. They update in place when the
  count is 1 and otherwise "shallowly clone" **[cited, from a repository mirror only]**.
- The older static analyses: Hudak and Bloss, "The aggregate update problem" (POPL 1985),
  and Schmidt's single-threaded stores (TOPLAS 1985) **[cited]**.
- The weakness is the one Huisinga's KIT thesis (2023) names: when uniqueness is broken by
  accident, an O(1) update silently becomes an O(n) copy. Its example is an array kept in a
  map, so that each `push` copies it **[checked: compilation.md §5.1, which read it]**.

**Monadic arrays.**
- Launchbury and Peyton Jones, "Lazy functional state threads" (PLDI 1994): `ST` and
  `runST`, encapsulated by a rank-2 type.
- Wadler's "Comprehending monads" (LFP 1990), as an answer to destructive array update.
- State can also be an algebraic effect handled by a handler (Plotkin and Pretnar, ESOP
  2009). I found no work on in-place arrays through handlers in particular **[cited;
  the last point unverified]**.

**Builtin types as inductive families.** Allais, "Builtin Types viewed as Inductive
Families" (ESOP 2023). A record of the efficient encoding plus an erased invariant, smart
constructors, and a "view" so users match as if on the inductive type
**[checked: compilation.md card C9, which read it]**.

### 2.2 Other languages

| System | What proofs see | How it runs | Link between them | Shared update | Bounds |
|---|---|---|---|---|---|
| **Lean 4** | `structure Array α where toList : List α`; every operation is defined on `toList` | a C dynamic array of boxed values; `ByteArray`/`FloatArray` packed | `@[extern "lean_array_fset"]` and `@[implemented_by]`: trusted, no axioms | in place when the count is 1, else an O(n) copy | `a[i]` needs a proof; `a[i]?` an `Option`; `a[i]!` panics; `setIfInBounds` |
| **Rocq** | opaque primitive `array A` with 11 axioms (`get_set_same`, `get_set_other`, `array_ext` …) | Baker version arrays in the kernel, VM and native compiler (`kernel/parray.ml`) | the axioms, plus trusted kernel reduction | persistent: old versions reroot | 63-bit indices; out of range gives a stored default; length ≤ 4,194,304 |
| **Haskell** | (no proofs) | `Data.Array` (`//` copies); `ST`/`STUArray`; `vector` with `modify`, in place "if it is safe to do so"; `IntMap`; linear-base arrays | — | copy, `ST`, or linear | runtime error, or `!?` |
| **Idris 2** | `IOArray`; contrib `Data.Linear.Array` with quantity 1 | `IOArray` | `unsafePerformIO`, trusted | in place, by linearity | `Maybe` / `Bool` results |
| **Agda** | `Data.Vec` (inductive) only; no array builtin | FFI postulates to Haskell or JS | trusted (`COMPILE` pragmas; "treated as postulates") | — | — |
| **F\*** | `FStar.Seq`, an abstract sequence (implemented as a list), with lemmas such as `lemma_index_upd1` | Low\*/Steel/Pulse heap arrays specified against `seq` | proof obligations | mutable heap | refinement types |
| **Isabelle** | `datatype 'a array = Array "'a list"` (AFP `Diff_Array`); `IArray` read-only | SML: Baker diff arrays; Scala a DiffArray | `code_printing`, trusted | persistent | — |
| **Dafny** | `seq` values; `array` heap objects with `reads`/`modifies` frames | arrays | proof obligations | mutable heap | `0 <= i < a.Length` proved |
| **Koka** | (no proofs) | `vector`, with Perceus reuse | — | in place when unique (for vectors, unverified) | `exn` or `maybe` |
| **OCaml** | (no proofs) | `Array`, `Float.Array`; Conchon–Filliâtre `parray` as a library | — | mutable | exception |
| **CakeML** | arrays are store values `Varray (list)`, updated by `LUPDATE` | the verified compiler | proved | mutable store | `Subscript` exception |

Sources for every row are in [§10](#10-sources). Two points matter most here:

1. **Lean's design is the only one that fits Stitchwort's rules as they stand.**
   - Its kernel sees an ordinary structure over `List`, so there is no new axiom. The
     manual puts it as "from the point of view of proofs, `Array α` is just a wrapper
     around `List α`".
   - The fast version is trusted compiler code, outside the kernel, as Stitchwort's
     runtime natives already are (DESIGN.md §13: natives "used only while a program or test
     runs … are not in the kernel's trusted base") **[checked: `DESIGN.md:973`]**.
   - Its cost is the accidental-sharing cliff. Lean's manual: "Updating a shared array …
     requires time linear in the size of the array". Its tools for this are
     `dbgTraceIfShared` and the compiler's IR trace **[cited]**.
2. **Rocq's primitive arrays are the warning.** They are axioms, and they appear in
   `Print Assumptions`. Since they shipped in 8.13, `dev/doc/critical-bugs.md` lists five
   critical bugs involving them **[cited]**:
   - arbitrary code execution on an irreducible `PArray.set`;
   - arbitrary code execution on arrays of floats;
   - a missing universe substitution in `lazy`;
   - array literals longer than `max_length` accepted by the type checker (found in 2026,
     fixed in 9.2.1 and 9.3.1);
   - the instructive one, conversion that "would compare the mutated version of primitive
     arrays instead of undoing mutation where needed" (8.13 to 8.16.0). Persistence and the
     kernel's equality check interact.

   Stitchwort's compact-text note already rejected this route for `Text`, for the same
   reasons: axioms, and the most trusted code of any option
   **[checked: `compact-text.md`, option C]**.

## 3. The options

### 3.1 What proofs see (the model)

**M1. A std record around a list (Lean).**
`type Array (a: Type) = { toList: List a }`, with every operation defined through
`toList`.
- No kernel change and no axiom.
- `DecEq` and `Show` come from `List`'s.
- `ext` is "same size and the same element everywhere", from `List`'s.
- In the checker, which runs the definitions, everything costs what it costs on lists. So
  `decide` and `rfl` over a 10-element array are fine, and over a million elements they are
  slow, as lists are.
- This is the shape `Text` already has (`MkText (chars: List Char)`), with the same
  bridges at run time **[checked: `std/core/Text.sw:14-15`; `compact-text.md`, "Bridges"]**.

**M2. The same, with the length in the type** (`Array a n`, Lean's `Vector`, Idris
`Vect`).
- `set` keeps `n` by its type, so a grid's rows stay rectangular for free. The 2024 day 4
  research found a Lean solution spending about 60 lines on `Array.set` lemmas to keep rows
  rectangular **[checked: SW-112's 22 Oct note]**.
- But `push` changes the type, and an array built from input has its size in a
  dependent pair.
- Lean has both: `Vector α n` is `{ toArray : Array α, size_toArray : toArray.size = n }`
  **[cited]**. So M2 is best as a *second* type over M1, later.

**M3. An opaque type specified by axioms.**
- It breaks the rule that exports are assumption-free, apart from `Quot.sound`
  **[checked: `DESIGN.md:123`]**.
- Proofs could no longer compute: nothing reduces in the checker.
- Ruled out.

**M4. A kernel primitive with reduction rules (Rocq).**
- Fast checker computation on big arrays.
- But it brings M3's axioms, a new value form in both kernel evaluators, conversion and
  hashing, and the bug history above.
- Nothing measured needs arrays in the checker. Day 15's proofs never compute 30 million
  turns, and its tests check the program against the spec for 300 turns
  **[checked: NOTES-2020 day 15]**.
- Ruled out now. Compact text's "B1" route (a compact *representation* of a list in the
  checker, with no new axioms) stays open if a proof ever needs a big closed array.

**M5. Over `Vec`, or over `Fin n → a`.** A function model makes `ext` need function
extensionality. Stitchwort has that through `Quot.funext`, but it is an axiom-backed
lemma, and it makes `DecEq` and `Show` harder **[checked: `std/Quot/Quot.sw`]**. A list is
simpler and has the lemma library already.

### 3.2 How `set` behaves at run time

**U1. Copy on every `set`.** Always O(n). Measured at 20,000 elements: 0.54 s for 20,000
turns in Node. At 30 million elements it would never finish **[ran]**. Useless for both
days.

**U2. In place when unshared, copy when shared (Lean, Koka, Roc).**
- Needs exact reference counts and moves on last use. The machine and native code have
  both **[checked: `crates/rt/src/code.rs:13-29`; in-place-reuse.md §1.1]**.
- The fastest possible when used linearly.
- The cliff is the accidental share: a shared `set` copies.

**U3. Version arrays (Baker; Rocq; Isabelle's SML code).**
- Needs nothing from the runtime, only hidden mutation inside the array.
- Every pattern of use is correct and never copies the whole array. Going back to an old
  version costs the number of steps back.
- Per operation it costs one small allocation (the `Diff` for the old version) and a check.
- Measured in Node, 30M turns of day 15's loop: 8.1 s, against 5.2 s for a plain JS array
  of `bigint`s **[ran]**.

**U4. A tree (Braun, `IntMap`, RRB) written in Stitchwort.**
- No natives and no runtime change. Every version stays fast.
- O(log n), with a path copied per update.
- Measured: a 25-level binary trie keyed by the number's bits ran day 15 at 8.4 µs a turn
  on the machine, against 12.3 µs for `Map`, so 1.5× better. Under `--js` and native it was
  *slower* than `Map` **[ran]**.
- So a library tree buys at most 2× here, not the 20–40× needed. A `Nat`-keyed map may
  still be worth having for sparse keys; that is a separate question.

**U5. A scoped mutable array behind an ability (`ST`-style).**
- `withArray size (() => …)`, with operations `read i` and `write i v`, handled by a
  state-passing handler.
- Stitchwort's handlers may resume more than once. So the handler can't promise the array
  is unique unless it copies on a second resumption, and that is U2's dynamic check again.
  The effect row says nothing about one-shot resumption.
- Each operation also pays the effect runtime's cost. On the effects benchmark that is
  tens of allocations per operation **[checked: in-place-reuse.md §2.2]**.
- Proofs about a handler are harder than proofs about values. Day 15's whole proof is about
  `Game` values **[checked: NOTES-2020 day 15]**.
- So it adds no guarantee, costs speed, and complicates proofs. It could be a thin library
  over a U2 array later, if someone wants the style.

**U6. A uniqueness or linear type** (Clean, Futhark, Idris 2, Linear Haskell). It would
give a *static* guarantee. But it is a type-system change across the language, and
compilation.md already set it aside because Stitchwort's reuse is dynamic and resumptions
share values **[checked: compilation.md item 18; in-place-reuse.md §3.3]**.

### 3.3 Where the fast version comes from

**B1. Natives bound by content hash** (today's mechanism for `Nat`, `Int`, `Text` and
`Float`).
- Each native names the std definition it replaces and that definition's hash.
- If the hash doesn't match, the definition runs as written, which is right but slow
  **[checked: `crates/rt/src/natives.rs:1-10`, `:153-182`]**.
- For arrays "slow" means O(n) per operation, so a 30M-turn run would hang (§6.2).

**B2. Proved refinement** (maps.md's D741 a): fast code written in Stitchwort, with
agreement theorems. An array's whole point is O(1) mutation, which can't be written in the
pure language, so this doesn't apply.

**B3. An attribute naming the native at the definition** (Lean's `@[extern]`). Simpler
to keep in step than a hash table. But the hash is stricter, because it notices any change
to what the native relies on, and it is the house mechanism.

## 4. Recommendation

M1 + U2 (machine, native, playground) + U3 (JS) + B1 with two changes to binding.

### 4.1 The library: `std/Array/Array.sw`

The model, in the house style:

```stitchwort
--| A sequence with constant-time access by position when run: `[3, 1, 2].toArray`.
--| To proofs it is its list of elements, and every operation is defined on that list.
type Array (a: Type) = { toList: List a }

def Array.size (array: Array a): Nat := array.toList.length
def Array.get (array: Array a) (index: Nat): Option a := array.toList.get index
def Array.getOr (array: Array a) (index: Nat) (fallback: a): a := array.toList.getOr index fallback
def Array.set (array: Array a) (index: Nat) (value: a): Array a := { toList = array.toList.set index value }
```

**The API**, with names taken from `List`, `Vec` and `Map` so they read the same:

| Group | Operations | Notes |
|---|---|---|
| Build | `Array.empty`, `Array.replicate (count := n) x`, `Array.tabulate n f` (`f: Nat → a`), `Array.fromList`, `List.toArray`, `Vec.toArray` | `replicate` is how day 15 starts: `Array.replicate (count := turns) 0` |
| Read | `size`, `isEmpty`, `get i: Option a`, `getOr i fallback`, `getLt i` with `[auto ok: i < array.size]`, `getFin (i: Fin array.size)`, `toList`, `toVec` | `get` returns an `Option`, as `List.get` and `Map.get` do; `getLt` follows `Vec.getLt` **[checked: `Vec.sw:129`]** |
| Change | `set i v`, `modify i f`, `swap i j`, `push v`, `pop: Option (Array a, a)` | out of range, `set` and `modify` leave the array unchanged, as `List.set` does **[checked: `Toolkit.sw:177-186`]**; nothing panics |
| Whole array | `map`, `mapWithIndex`, `foldLeft`, `foldRight`, `any`, `all`, `count`, `find`, `findIndex`, `zipWith`, `withIndex`, `sum` | each defined through `toList`, native when it pays (below) |
| Instances | `DecEq`, `Show` (as `[3, 1, 2].toArray`), `Ord` | by hand from `List`'s, as library types are **[checked: maps.md §4.1]** |

Bounds: three ways to read, and no fourth that can fail. An index the program can't prove in
range uses `getOr` (day 15) or `get`. One it can prove uses `getLt`. This matches Lean's
`a[i]?`, `getD` and `a[i]` (with proof), without `a[i]!`'s panic, since pure Stitchwort code
has no panic **[cited: Lean manual; inferred for Stitchwort]**.

**The lemmas** to ship. Each is a short proof from a `List` lemma, and most from
`List.getSet`, `List.getSetOther` and `List.lengthSet`, which exist
**[checked: `std/List/Lemmas.sw:2536-2549`]**.

- `getSet` (`i < a.size → (a.set i v).get i = Some v`), `getSetOther`, `getOrSet`,
  `getOrSetOther`, `sizeSet`, `getModify`, `getSwap`.
- `sizePush`, `getPush`, `getPushLast`, `popPush`.
- `getReplicate`, `getTabulate`, `sizeReplicate`, `sizeTabulate`, `getMap`, `sizeMap`,
  `foldLeftToList`.
- `ext`, a theorem (`a.size = b.size → (∀ i, a.get i = b.get i) → a = b`), and
  `toListInjective`.
- `getLtGet` and `getOrGet`, linking the three ways to read.
- `toListFromList`, `fromListToList`, `toVecToList`.

**2-D grids** are not a new type in this step. A grid is a record holding `width`, `height`
and `cells: Array a`, with the invariant `cells.size = width * height` kept by `sizeSet`;
reading at (row, column) is `cells.getOr (row * width + column)`. For 2020 day 11 the first
step is smaller: `Aoc.Common`'s `Grid.lookup` builds an `Array (Array a)` table instead of
maps, and only its lemma `lookupAt` is re-proved (§1.3). A std `Grid` comes once two or
three days have used the pattern (Q8).

### 4.2 Machine, native code and the playground

**The value.** A new `Value` variant, `Array(Rc<ArrayBuf>)`, where `ArrayBuf` holds a
`Vec<Value>`.
- This is what compilation.md §5.1 sketched.
- It has the precedent of `Value::Text(Rc<str>)` **[checked: `crates/rt/src/value.rs:38`]**.
- `Value` is `repr(u8)` and its layout is probed by native code, so the new variant goes
  through `native_abi::probe_layout`, the census and the trace like the others
  **[checked: `value.rs:19-23`]**.

**The natives.** About 15, bound by hash, implemented once in Rust, and shared by the
machine, native code and the WebAssembly playground (native code calls the machine's
leaves) **[checked: in-place-reuse.md §5]**.

- **O(1):** `size`, `get`, `getOr`, `getLt`, `set`, `modify`, `swap`, amortised `push`,
  `pop`.
- **O(n) loops:** `replicate`, `tabulate`, `fromList`, `toList`, `map` (in place when
  unique and the element type allows), `foldLeft`, `any`, `count`, `zipWith`.
- Higher-order natives (`map`, `foldLeft`, `modify`) call back into the machine. If that
  proves awkward in stage 2, they stay definitions over `get`, `set` and `size`, which are
  native. That is slower by a constant factor only **[inferred]**.

**In-place `set`**, the one new piece of runtime machinery.
- Today a primitive operation borrows its arguments: `prims::eval(s, op, args: &[&Value])`
  **[checked: `crates/rt/src/prims.rs:401`]**. So a `set` could never see a count of 1:
  the register still holds the array.
- The change is a short list of *consuming* natives (`set`, `modify`, `swap`, `push`,
  `pop`). Their first operand is taken out of its register when this is its last use (the
  `MOVE` bit `code.rs` already sets), and handed over owned.
- The native then calls `Rc::get_mut`. If the array is unique, it changes the buffer in
  place. If it isn't, it clones the buffer and bumps a copy counter.
- The decision is dynamic, so it stays correct when a resumption shares the array
  **[inferred from in-place-reuse.md §3.3]**.
- No `unsafe`: `Rc::get_mut` is safe Rust.

**Bridges**, as for `Text`.
- The checker's `Array` is a record around a list. So user code that reads `.toList`, or
  builds `{ toList = xs }`, gets an O(n) conversion loop at that point. It gets no other
  cost.
- Every std operation is native, so that happens only when the user asks for the list
  **[checked: compact-text.md "Bridges" for the precedent]**.

**The copy counter.** Copies made by a shared `set`, and their total size, are counted in
the run statistics. `stitchwort run` prints a one-line note at the end of a run where they
exceeded, say, ten copies of over 1,000 elements: "Array.set copied a shared array 30,000
times (largest 29,469,423 elements): see the guide's 'Keeping arrays unshared'" (Q5).
That is the diagnostic Lean has (`dbgTraceIfShared`) but automatic. It belongs with
in-place-reuse.md's per-site report (§5).

**Packed buffers, later.**
- A `Value` is 3 words (24 bytes) **[checked: `value.rs:21`]**, so 30 million `Nat`s take
  720 MB.
- For comparison **[ran]**: a JS array of `bigint`s used 507 MB, an `Int32Array` 149 MB, and
  a Python list 354 MB.
- `ArrayBuf` can later hold `Vec<u64>` while every element is a small `Nat`, changing to
  boxed values on the first element that isn't. That is invisible to the API. Lean instead
  has separate types (`ByteArray`, `FloatArray`) **[cited]**.
- Only if stage 2's measurements show memory matters (Q9).

### 4.3 JS: version arrays

- An `Array` is a small object. The newest version holds the JS array, and an older version
  holds `{ index, value, next }`.
- `get` and `set` on the newest version are a check plus the access. On an older version
  they first reroot, in a loop, never recursion, so they are stack-safe at any depth.
- `set` allocates one object for the version it leaves behind. If nothing keeps that
  version, the garbage collector frees it young.
- This is Conchon and Filliâtre's array and Rocq's `kernel/parray.ml`
  (`Array of … | Updated of int * 'a * 'a t`, with `reroot`) **[cited]**.
- A 40-line prototype ran day 15's 30M turns in 8.1 s and 1.17 GB, against 5.2 s and
  507 MB for a plain array, and read old versions correctly **[ran: `baker.js`, §7]**.

The other choices for JS:
- **Copy on `set`** is unusable (U1).
- **Track uniqueness in generated JS**: there are no counts to track it with.
- **A 32-way persistent trie** (Clojure, RRB) is O(log₃₂ n), allocates a path per `set`,
  and is more code to trust than version arrays. Not measured here.

At the boundary an `Array T` crosses as a TS array, as `List T` does today
(`readonly T[]` as a parameter, `T[]` elsewhere) **[checked: `crates/js/src/lib.rs:81`]**.
Decoding builds the newest version from a copy. Encoding reroots and copies out.

**As built (SW-1638, D2462).** `VERSION_ARRAYS` in `crates/js/src/lib.rs`: a version is
one object shape, `{ items, op, index, value, next }`, where the newest has `items` and an
older one a `set`, `push` or `pop` change (`op`) towards `next`. The same natives as the
machine's are bound by hash through `bind_array`, all or nothing (`E-BUILTIN`); the
record's constructor is `arrayOfList` and its match `listOfArray`, made only if the branch
reads the list. `push` on an empty array makes a fresh one, so the shared `Array.empty`
constant never becomes a change. At the boundary `Array T` is `Boundary::Array`, a `T[]`;
encoding copies the elements out before encoding any, since encoding one could reroot the
array (a `Tree` holding an older version of the array it is in). Day 15 on its input
**[ran]**: 23 s user (57 s real, the machine loaded), 3.0 GB peak, the same answers;
before, 127 s. 100,000 `set`s on one array finish in a few seconds
(`crates/cli/tests/run_js.rs`).

Small `Nat`s are `bigint` in generated JS. That is a large share of the 5.2 s against the
0.52 s of an `Int32Array` **[ran]**, and it is compilation.md's T5/D1922 question, separate
from this note.

### 4.4 Binding, and SW-1582

Natives today bind one by one. A definition whose hash has drifted quietly runs as written,
and a test notices. SW-1582 was that case: `Int.decEq` lost its native, and the failing
tests went unseen until a review **[checked: `board/board show 1582`]**. For `Text` a lost
native costs a constant factor. For `Array` it would cost O(n) per operation through the
bridges: a 30M-turn run that quietly never ends. So:

1. **All or nothing.** The array representation applies only when the data type's hash
   and every array native's hash match. That is how `Int`'s and `Text`'s representations
   already gate their natives **[checked: `natives.rs:187-262`]**.
2. **Loud, not slow.** If the `Array` type is loaded and any of them doesn't match, the
   program is refused with an `E-BUILTIN` error that names the definition. That is
   compact-text's policy for a representation literals depend on
   **[checked: compact-text.md, "Policy when they don't match"]**.
   - std is compiled into the binary, so only a developer changing std can ever see it,
     and they see it at once.
   - The binding test also runs in the fast `std` lane, so the lane that changes the
     definition fails before review.

### 4.5 The checker, the reference evaluator, hashing and caches

- **The kernel and the checker:** no change. They run the list definitions. No native is
  in the kernel's trusted base (DESIGN.md §13).
- **`run --reference`:** list speed, O(n) per operation. Day 15 part 2 is already out of
  its reach. A future differential test of a big array program would skip the reference
  run, as maps.md accepted for maps **[checked: maps.md §5, risk 3]**.
- **Hashing:** an array value is never hashed. Content hashes are of declarations, and a
  closed array in a definition is the record of a list. New std declarations change the
  std hashes they touch, so the brief for stage 1 asks for `snap:hashes` and the
  `hash_stability` test **[checked: memory note "Example hash snapshots"]**.
- **The check cache** keys on declaration hashes and the binary's fingerprint. Natives
  live in the binary, so a change to one invalidates as any compiler change does
  **[inferred from `crates/web/src/lib.rs:161`, `SOURCE_FINGERPRINT`]**.
- **The playground** runs the machine compiled to WebAssembly, so it gets U2 unchanged.
  Its memory ceiling is the open question: wasm32 has 4 GB at most, and a 30M-element
  array of boxed values is 720 MB on 64-bit Rust (less in wasm32, where pointers are 4
  bytes) **[inferred]**. To measure in stage 2 (§8).

### 4.6 What day 15 and day 11 become

**Day 15.**
- `lastSeen: Array Nat`, of size `turns`, with 0 meaning "not spoken yet" (turns count
  from 1). A turn is `getOr` and `set`.
- The invariant in `Game.sw` is restated over `getOr` instead of `Map.get`, with
  `getOrSet`/`getOrSetOther` in place of `getInsert`/`getInsertOther`. The rest of the
  proof is unchanged **[inferred from the proof's outline in NOTES-2020]**.
- `Starting.next` computes `starting.numbers.length` every turn. In the scratch loop that
  alone was 0.5 µs a turn (§7), so the day should hoist it once arrays make it matter.

**Day 11.**
- `Grid.lookup` builds an array table, and `lookupAt` is re-proved once in `Aoc.Common`.
- The day itself changes not at all.

### 4.7 Docs

The guide gets an "Arrays" section in `06-namespaces-and-library.md` or its own page:
`getOr` or `getLt`, `set`, the cost model ("in place when nothing else holds the array"),
and how to keep an array unshared (pass it on, don't keep the old one). `docs/syntax.md`
gets the new names, and the feature tour a page, since a newcomer would enjoy it: "a
30-million-turn game in a few seconds, with a proof".

## 5. How this relates to the in-place reuse plan

in-place-reuse.md (SW-1159) found that the machine and native code already have most of
Perceus: moves on last use, early drops, and reuse of a unique cell by the next
constructor. Its plan (D2273–D2277) widens that: a per-site reuse report, then reuse across
small helpers, hand reuse in the effect runtime, and borrowed parameters only if needed.

**In-place array update depends on none of those stages.** It needs exact counts and moves
on last use, which exist today, plus its own consuming natives (§4.2). It can be built
before, after or alongside the plan.

The two meet in three places:

1. **The diagnostic.** The reuse report (D2274, stage 1) and the array copy counter are
   the same kind of thing: "where did sharing stop an in-place update?" They should share
   the trace hooks and the output. If stage 1 lands first, the array counter is one more
   event kind in it. If arrays land first, the counter is the report's first customer
   **[inferred]**.
2. **Field reads.** A record's field read while the record is still live clones the field,
   which is an increment **[checked: `code.rs:807-813`, `Instr::Field`]**.
   - `opt.rs` already folds a `let` of one projection into the arm of a match on the
     record, so later projections need no test **[checked: `opt.rs:837-870`]**.
   - Whether `game.lastSeen.set …` in day 15's natural `say` gets the array uniquely
     depends on the order these clones and drops come in. That is exactly what the report
     shows. Evidence to collect in stage 2 (§8): the copy counter on the natural program
     must read 0.
3. **Borrowed parameters** (stage 3 of that plan) would make read-only calls *on* an
   array cost no increment. Array reads are primitives, which already borrow, so arrays
   don't add a reason to do that stage.

The JS backend is outside that plan, as it is outside reference counting. That is why §4.3
is a different mechanism.

## 6. Risks

### 6.1 Accidental sharing: the cliff

The risk that matters. A `set` on a shared array is an O(n) copy, and the program is still
correct, so nothing fails. Huisinga's example is an array kept in a `Map`, so each `push`
copies it; the cure there was taking the entry out of the map before changing it. Others:

- an array kept for a second pass;
- an array captured by a live closure;
- an array held by a resumption;
- the old version kept "just in case", as in `let before := game.seen` followed by
  `game.seen.set …`.

Mitigations:
- the copy counter and its end-of-run note (§4.2);
- the guide section (§4.7);
- a test per std operation that a threaded loop of 10^5 `set`s makes 0 copies.

On JS the cliff doesn't exist: version arrays degrade gently. So the same program can be
fast on JS and slow on the machine. The note in `run` says which line to look at
**[inferred]**.

### 6.2 A native that drifts

Covered by §4.4: all or nothing, and an error, not a fallback.

### 6.3 Natives that disagree with their definitions

Each native joins the trusted list in DESIGN.md §13. The tests follow text's:
- every `-- run:` case in a new `examples/extract/array.sw`, with natives on and off;
- a property test of random operation sequences against the list definitions, including
  out-of-range indices, `pop` on empty, and old versions read after newer ones (for JS);
- 10^6-element runs to show stack safety;
- for the machine, a sequence that shares an array mid-way, to show copy-then-change keeps
  the old version.

**[checked: compact-text.md "Tested", for the pattern]**.

### 6.4 Proofs over big arrays stay slow

The checker sees lists. A proof that computes over a closed million-element array is as
slow as one over a million-element list. Nothing today does that. If something does
later, compact text's B1 (a compact list form in the checker, no axioms) is the route
(M4's note).

### 6.5 Memory

24 bytes an element on the machine (§4.2), against 8 in a Python list or a JS array of
small integers. Fine for AoC sizes. The packed buffer (Q9) is the remedy if needed.

## 7. Measurements

All **[ran]**, 6 Nov 2026, as described in the labels at the top. Scratch files are under
the session scratchpad (`array/`), not in the repository. Each Stitchwort figure is the
program's time minus the same program run for 1 turn, which is how the cost of checking
and building was taken out (0.22–0.25 s).

**Day 15's loop, written to swap the structure that holds "last seen"** (`map.sw`,
`trie.sw`, `list.sw`, `none.sw`, `none6.sw`). It is the same game as the day, with the
starting numbers inlined. The output was checked: `map` and `trie` agree (380 at turn
200,000), and the Python, JS and Baker versions give 41687 at 30M, the day's answer.

| variant | turns | machine (`run`) | `--js` | `--native` | per turn, machine |
|---|---|---|---|---|---|
| `Map Nat Nat` (today) | 200,000 | 2.47 s | 0.28 s | 0.29 s | 12.3 µs |
| 25-level binary trie in Stitchwort (U4) | 200,000 | 1.67 s | 0.43 s | 0.38 s | 8.4 µs |
| `List Nat`, `List.set` (O(n)) | 20,000 | 2.07 s | — | — | 104 µs |
| no structure, loop only, with `start.length` each turn | 1,000,000 | 0.67 s | — | — | 0.67 µs |
| no structure, loop only, length a constant | 1,000,000 | 0.17 s | 0.02 s | 0.04 s | 0.17 µs |
| … plus one `Text` native call per turn | 1,000,000 | 0.21 s | — | — | 0.21 µs |

- At 200,000 turns the map holds about 25,000 keys, so the per-turn `--js` and native costs
  here are lower than the day's 30M-turn figures (4.2 and 2.8 µs, with 3.6M keys and a
  deeper tree). The machine's 12.3 µs matches the day's 11.9.
- The last row prices a native call on the machine at about 0.04 µs.

**The same loop outside Stitchwort, 30M turns** (`d15.js`, `baker.js`, `d15.py`):

| variant | time | peak memory |
|---|---|---|
| Node, `Int32Array` of numbers | 0.52 s | 149 MB |
| Node, JS `Array` of `bigint`s, in place | 5.16 s | 507 MB |
| Node, Baker version array of `bigint`s (§4.3) | 8.06 s | 1,170 MB |
| Node, JS `Map` of `bigint`s | 11.79 s | 523 MB |
| Node, copy the array on every `set` | 0.54 s for 20,000 turns at 20,000 elements; quadratic | — |
| Python, `list` | 7.17 s | 354 MB |
| Python, `dict` | 10.11 s (the notes measured 7.2 s on a quieter machine) | 555 MB |

**The estimate** for day 15 part 2 with the recommended array **[inferred]**:

- **Machine:** the loop at 0.17–0.67 µs a turn (depending on hoisting `length`), plus two
  native calls at about 0.04 µs each, plus cache misses on a 720 MB buffer. About
  **8–20 s**, against 357 s.
- **Native:** the loop at about 0.04 µs a turn, plus the same natives and misses. About
  **2–5 s**, against 84 s.
- **JS:** the plain array's 5.2 s times the version array's 1.55×, plus generated-code
  overhead. About **10–25 s**, against 127 s.
- **Python:** 7–10 s.

For day 11, lookups at about 0.1 µs instead of 1.7 µs would take a round from about
0.12 s to about 0.02 s. That puts `main`'s 160 rounds in the low seconds, against 19 s
**[inferred]**.

Not measured, because it needs a build (the daily tier had the machine): any prototype of
the natives on the machine or native code. See §8.

## 8. Staged plan, and the evidence still to collect

| Stage | What | Size | Model |
|---|---|---|---|
| 1 | `std/Array/Array.sw`: the model, the API of §4.1, the lemmas, the instances, tests; `Vec`/`List` conversions; `snap:hashes`. Runs at list speed everywhere | 1 lane-day | Sonnet |
| 2 | Machine, native code and playground: `Value::Array`, consuming natives, bridges, the binding table (all or nothing, `E-BUILTIN`), the copy counter, differential and property tests; day 15 and `Grid.lookup` moved to it and measured | 2 lane-days | Opus (runtime ownership, native ABI) |
| 3 | JS: version arrays, natives, boundary codec, the same tests under Node | 1–1.5 lane-days | Sonnet, with the §4.3 prototype as its spec |
| 4 | Docs: the guide section, `syntax.md`, a feature-tour page; NOTES-2020 updates for days 11 and 15 | 0.5 lane-day | Sonnet |
| later | packed `Nat` buffers (Q9); a std `Grid` (Q8); a sized `Array.Of n` (Q2); `withArray`-style ability (U5) only if asked | — | — |

Stage 1 isn't merged on its own (maps.md's D749 precedent). A user who reached for an
"array" would get list speed and a worse surprise than `Map`. Stages 1 and 2 merge together.
Stage 3 follows directly. Until it lands, `run --js` on an array program refuses with a
clear message rather than running at list speed, as `--js` already refuses a `Text` without
its representation **[checked: natives.rs `TEXT_DATA_HASH` doc]**.

**Evidence still to collect**, in stage 2 unless marked:

1. Day 15 part 2 timed on all three runtimes with the natural program, against §7's
   estimate. If the machine is over 30 s, find out why before stage 3.
2. **The copy counter reads 0** on day 15's natural `Game.say`. If not, decide between a
   compiler fix (projection order, §5 item 2) and a documented idiom.
3. Day 11 with the array-backed `Grid.lookup`, all three runtimes, and the other 14 users
   of `.lookup` unchanged in output.
4. Peak memory of day 15 on the machine (expected about 750 MB), and whether the playground
   in Chrome and Safari can hold a 30M-element array. That decides how soon Q9 comes.
5. Stage 3: generated JS with version arrays against the hand-written 8.1 s.
6. A property test that interleaves old and new versions finds no disagreement on any
   runtime.

## 9. Decisions

Each question has a recommendation. The orchestrator assigns the D numbers.

- **Q1. What proofs see.** (a) A std record around a list, with operations defined on
  the list (Lean), and no kernel change / (b) an opaque type with axioms / (c) a kernel
  primitive like Rocq's / (d) over `Fin n → a`. **[rec: (a).** No axiom, no new kernel
  code, and the list lemmas carry over. Rocq's route brought 11 axioms and five critical
  bugs.**]**
- **Q2. Length in the type.** `Array a` now, with a sized wrapper (`Array.Of n a`, Lean's
  `Vector`) only once a program needs it / sized from the start. **[rec: unsized now.**
  `push` and input-sized arrays are simpler, and `sizeSet` keeps grids rectangular in one
  line.**]**
- **Q3. Update on the machine, native code and the playground.** In place when unshared,
  copy when shared (Lean, Koka, Roc), through consuming natives / version arrays there
  too / copy always. **[rec: in place when unshared.** The runtime already counts
  references and moves on last use, so linear code is as fast as it can be. Version
  arrays would add an allocation per `set` for a case the copy counter can expose
  instead.**]**
- **Q4. Update in JS.** Version arrays (Baker; Conchon–Filliâtre) / a 32-way persistent
  trie / copy on `set`. **[rec: version arrays.** O(1) when used linearly, correct and
  never a full copy otherwise. 1.55× a plain array in the prototype.**]**
- **Q5. Accidental sharing.** A copy counter in the run statistics, with an end-of-run
  note past a threshold, joined to in-place-reuse.md's report / only the report / nothing.
  **[rec: counter and note.** It is the cliff every refcounting design has, and Lean needs
  a manual trace to find it.**]**
- **Q6. Binding.** Array natives bind all or nothing, and a mismatch is an `E-BUILTIN`
  error, with the binding test in the fast `std` lane / bind one by one with silent
  fallback, as for `Text` today. **[rec: all or nothing, loud.** A silent fallback here is a
  hang, and SW-1582 shows drift goes unseen.**]**
- **Q7. API and bounds (§4.1).** `get` returns `Option`; `getOr`; `getLt` with an `auto`
  proof; `getFin`; `set`/`modify` out of range leave the array unchanged; `push`/`pop`;
  names as in `List`. **[rec: approve as listed.]**
- **Q8. Grids.** Back `Aoc.Common`'s `Grid.lookup` with arrays now (day 11 and 14 others,
  one lemma re-proved), and a std `Grid` only after two or three days use the pattern /
  a std `Grid` now. **[rec: `Aoc.Common` now, std later.]**
- **Q9. Packed number buffers.** Only if stage 2 shows memory matters (day 15 at about
  750 MB, or the playground can't hold it) / build with stage 2. **[rec: only if
  measured.]**
- **Q10. Order and staging (§8).** Stages 1 and 2 merge together, stage 3 next, docs
  last; the array doesn't wait for D2273–D2277, but its counter joins the reuse report
  when both exist. **[rec: yes.]**

For the orchestrator, not Matt: SW-112 is this ticket's older twin and can be closed into
SW-1473 once these are answered. compilation.md's D1920 and T6 are answered by this note.

## 10. Sources

Papers:

- H. G. Baker, "Shallow binding in Lisp 1.5", CACM 21(7), 1978:
  <https://dblp.org/rec/journals/cacm/Baker78a.html>; MIT WP-138:
  <https://dspace.mit.edu/handle/1721.1/41975>
- H. G. Baker, "Shallow binding makes functional arrays fast", SIGPLAN Notices 26(8), 1991:
  <https://doi.org/10.1145/122598.122614>
- S. Conchon, J.-C. Filliâtre, "A Persistent Union-Find Data Structure", ML Workshop 2007:
  <https://usr.lmf.cnrs.fr/~jcf/publis/puf-wml07.pdf>; code and Coq proofs:
  <https://usr.lmf.cnrs.fr/~jcf/puf/>
- S. Conchon, J.-C. Filliâtre, "Semi-persistent Data Structures", ESOP 2008:
  <https://doi.org/10.1007/978-3-540-78739-6_25>
- M. E. O'Neill, F. W. Burton, "A new method for functional arrays", JFP 7(5), 1997:
  <https://doi.org/10.1017/S0956796897002852>
- C. Allain, B. Clément, A. Moine, G. Scherer, "Snapshottable Stores", ICFP 2024:
  <https://doi.org/10.1145/3674637>
- C. Okasaki, *Purely Functional Data Structures*, CMU-CS-96-177 (1996) and CUP (1998):
  <https://www.cambridge.org/core/books/purely-functional-data-structures/0409255DA1B48FA731859AC72E34D494>
- C. Okasaki, "Purely functional random-access lists", FPCA 1995 (via the book)
- C. Okasaki, "Three algorithms on Braun trees", JFP 7(6), 1997:
  <https://www.cambridge.org/core/product/59CF6B17F75EC216EBCA8A08E8780DFF>
- R. Hinze, R. Paterson, "Finger trees", JFP 16(2), 2006:
  <https://doi.org/10.1017/S0956796805005769>
- P. Bagwell, "Ideal Hash Trees", EPFL 2001: <https://lampwww.epfl.ch/papers/idealhashtrees.pdf>
- P. Bagwell, T. Rompf, "RRB-Trees: Efficient Immutable Vectors", EPFL 2011:
  <https://infoscience.epfl.ch/items/c11dbc7a-2601-4228-b42b-466aa313f589>
- N. Stucki, T. Rompf, V. Ureche, P. Bagwell, "RRB vector", ICFP 2015:
  <https://doi.org/10.1145/2784731.2784739>
- C. Okasaki, A. Gill, "Fast Mergeable Integer Maps", ML Workshop 1998:
  <https://ku-fpg.github.io/papers/Okasaki-98-IntMap>
- P. Wadler, "Linear types can change the world!", 1990:
  <https://homepages.inf.ed.ac.uk/wadler/topics/linear-logic.html>
- E. Barendsen, S. Smetsers, "Uniqueness typing for functional languages with graph
  rewriting semantics", MSCS 6(6), 1996: <https://doi.org/10.1017/s0960129500070109>
- T. Henriksen et al., "Futhark: purely functional GPU-programming with nested parallelism
  and in-place array updates", PLDI 2017: <https://doi.org/10.1145/3062341.3062354>
- J.-P. Bernardy et al., "Linear Haskell", POPL 2018: <https://doi.org/10.1145/3158093>
- C. McBride, "I Got Plenty o' Nuttin'", 2016: <https://researchr.org/publication/McBride16>
- R. Atkey, "Syntax and Semantics of Quantitative Type Theory", LICS 2018:
  <https://doi.org/10.1145/3209108.3209189>
- E. Brady, "Idris 2: Quantitative Type Theory in Practice", ECOOP 2021:
  <https://doi.org/10.4230/LIPIcs.ECOOP.2021.9>
- A. Lorenzen et al., "Oxidizing OCaml with Modal Memory Management", ICFP 2024:
  <https://doi.org/10.1145/3674642>
- S. Ullrich, L. de Moura, "Counting Immutable Beans", IFL 2019:
  <https://arxiv.org/abs/1908.05647>
- A. Reinking, N. Xie, L. de Moura, D. Leijen, "Perceus", PLDI 2021:
  <https://doi.org/10.1145/3453483.3454032>
- A. Lorenzen, D. Leijen, "Reference counting with frame limited reuse", ICFP 2022:
  <https://doi.org/10.1145/3547634>
- A. Lorenzen, D. Leijen, W. Swierstra, "FP²: Fully in-Place Functional Programming",
  ICFP 2023: <https://doi.org/10.1145/3607840>
- P. Hudak, A. Bloss, "The aggregate update problem in functional programming systems",
  POPL 1985: <https://doi.org/10.1145/318593.318660>
- J. Launchbury, S. Peyton Jones, "Lazy functional state threads", PLDI 1994:
  <https://doi.org/10.1145/178243.178246>
- P. Wadler, "Comprehending monads", LFP 1990: <https://doi.org/10.1145/91556.91592>
- G. Plotkin, M. Pretnar, "Handlers of algebraic effects", ESOP 2009:
  <https://doi.org/10.1007/978-3-642-00590-9_7>
- G. Allais, "Builtin Types viewed as Inductive Families", ESOP 2023:
  <https://arxiv.org/abs/2301.02194>
- M. Armand, B. Grégoire, A. Spiwack, L. Théry, "Extending Coq with Imperative Features and
  its Application to SAT Verification", ITP 2010: <https://hal.archives-ouvertes.fr/inria-00502496>
- L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language", CADE 2021:
  <https://doi.org/10.1007/978-3-030-79876-5_37>
- P. Lammich, "Refinement to Imperative HOL", JAR 62(4), 2019:
  <https://doi.org/10.1007/s10817-017-9437-1>
- J. Huisinga, master's thesis on static uniqueness for Lean arrays, KIT 2023:
  <https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf>

Languages:

- Lean: Arrays in the reference manual <https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/>;
  `Array.set` with `@[extern "lean_array_fset"]` in
  <https://github.com/leanprover/lean4/blob/master/src/Init/Data/Array/Set.lean> (read
  6 Nov, lines 29-32); `structure Array` in `src/Init/Prelude.lean`; `lean.h`
  (`lean_array_object`, `lean_ensure_exclusive_array`); lemmas in
  `src/Init/Data/Array/Lemmas.lean`; `Vector` <https://lean-lang.org/doc/api/Init/Data/Vector/Basic.html>;
  `ByteArray` <https://lean-lang.org/doc/reference/latest/Basic-Types/Byte-Arrays/>;
  reference counting and `dbgTraceIfShared`
  <https://lean-lang.org/doc/reference/4.33.1/Run-Time-Code/Reference-Counting/>
- Rocq: primitive objects <https://rocq-prover.org/doc/master/refman/language/core/primitive.html>;
  `theories/Corelib/Array/PrimArray.v` and `ArrayAxioms.v` (11 axioms, counted 6 Nov) in
  <https://github.com/rocq-prover/rocq>; `kernel/parray.ml` (`Updated`, `reroot`);
  `dev/doc/critical-bugs.md` <https://github.com/coq/coq/blob/master/dev/doc/critical-bugs.md>
  (the five array entries, read 6 Nov); the stdlib's `PArray.v`
  <https://github.com/rocq-prover/stdlib/blob/master/theories/Array/PArray.v>
- Haskell: `Data.Array` <https://hackage-content.haskell.org/package/array/docs/Data-Array.html>;
  `Data.Array.ST` <https://hackage-content.haskell.org/package/array/docs/Data-Array-ST.html>;
  `Data.Vector` <https://hackage-content.haskell.org/package/vector-0.13.2.0/docs/Data-Vector.html>;
  `Data.IntMap.Strict` <https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-IntMap-Strict.html>;
  linear-base `Data.Array.Mutable.Linear`
  <https://hackage-content.haskell.org/package/linear-base/docs/Data-Array-Mutable-Linear.html>;
  the old `Data.Array.Diff` <https://hackage.haskell.org/package/array-0.2.0.0/docs/Data-Array-Diff.html>
- Idris 2: `Data.IOArray` <https://www.idris-lang.org/Idris2/base/docs/Data.IOArray.html>;
  `Data.Linear.Array` <https://idris-lang.org/Idris2/contrib/source/Data.Linear.Array.html>;
  <https://github.com/stefan-hoeck/idris2-array>
- Agda: built-ins <https://agda.readthedocs.io/en/latest/language/built-ins.html>; FFI
  <https://agda.readthedocs.io/en/latest/language/foreign-function-interface.html>; stdlib
  <https://github.com/agda/agda-stdlib/tree/master/src/Data>
- OCaml `Float.Array` <https://ocaml.org/manual/latest/api/Float.Array.html>; F\*
  `FStar.Seq.Base` <https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Seq.Base.fsti>;
  Koka `std/core/vector` <https://github.com/koka-lang/koka/blob/dev/lib/std/core/vector.kk>;
  Roc builtins (mirror) <https://git.joshthomas.dev/language-servers/roc/src/commit/0a42a04765ff92a4f0069f113a48ec1c6134d2fc/compiler/builtins/docs/List.roc>;
  Clean Language Report 2.1 §4.4 <https://www.cs.ubbcluj.ro/~csatol/log_funk/clean/CleanLangRep.2.1.pdf>;
  Futhark <https://futhark.readthedocs.io/en/latest/language-reference.html>; Dafny types
  <https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Types.md>; Isabelle
  `IArray` <https://isabelle.in.tum.de/library/HOL/HOL-Library/IArray.html> and AFP
  `Diff_Array` <https://github.com/isabelle-prover/mirror-afp-devel/blob/master/thys/Collections/Lib/Diff_Array.thy>;
  CakeML `semanticPrimitivesScript.sml` <https://github.com/CakeML/cakeml/blob/master/semantics/semanticPrimitivesScript.sml>

In this repository: `docs/research/compilation.md` §5.1 and D1920;
`docs/research/in-place-reuse.md`; `docs/proposals/compact-text.md`, `maps.md`,
`fast-runtime.md` §2.4, `float.md`; `crates/rt/src/{natives,value,code,prims,opt}.rs`;
`DESIGN.md` §11–13; `aoc/NOTES-2020.md` days 11 and 15; SW-112, SW-1582.
