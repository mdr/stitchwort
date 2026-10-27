# Proposal: length-indexed vectors (`Vec`) and day 4 over them

> **Status (20 Oct 2026):** D133 yes and D135 (a): indexed data types go into the kernel first (SW-178); this note's representation decisions (D126-D132, D134) wait until then (SW-179, SW-180).
>
> **Built (SW-179, D191):** `Vec` is the indexed data type (option C), chosen by measurement, in `std/Vec/Vec.sw`, with `Fin` in `std/Fin/Fin.sw`. See [As decided](#as-decided); §0-§8 below are draft 1, written before families existed.

**Status:** draft 1, 20 October 2026. Waiting for review (design-review gate). Nothing is
built yet. Decisions D124 and D125 (Matt, 20 October) set the direction; the open questions
are D126 to D133 in [§8](#8-decisions-wanted).

This note can be read without knowing the codebase: §1 describes the parts of Stitchwort it
touches, checked against the source on `main` at `a576fae`. Claims about other systems cite
their sources. Anything not checked against a source is marked **unverified**.

## Contents

0. [Summary](#0-summary)
1. [Background: Stitchwort today](#1-background-stitchwort-today)
2. [What day 4 needs](#2-what-day-4-needs)
3. [How other systems do it](#3-how-other-systems-do-it)
4. [Representation options](#4-representation-options)
5. [Indexing](#5-indexing)
6. [The library file](#6-the-library-file)
7. [Day 4 over `Vec`](#7-day-4-over-vec)
8. [Decisions wanted](#8-decisions-wanted)
9. [As decided](#as-decided)
10. [Sources](#sources)

## 0. Summary

- `Vec a n` is **a record of a list and a proof of its length**:
  `type Vec (a: Type) (n: Nat) = { list: List a, len: List.length list = n }`. This is what
  Lean 4 (core `Vector`: an `Array` and a size proof) and Mathlib (`List.Vector`: a list and a
  length proof) do. It works in Stitchwort today, with no kernel change: I checked a scratch
  file with this type, a `map` and a grid record. At run time it is the list (the proof is
  erased), so it costs no more than the lists day 4 uses now. Every `List` lemma carries over.
- An indexed data type (`VNil: Vec a 0`, `VCons: … -> Vec a (Succ n)`, as in Agda and Idris)
  would need **indices in the kernel**, which has parameters only, with equality the one
  built-in exception. That is a change to the trusted core, so it is out of scope here.
- Indexing is `Vec.get (v: Vec a n) (i: Nat) [auto ok: i < n]: a`, an ordinary `Nat` with a
  proof that `auto` finds for literals, as Lean's `v[i]` takes. A `Fin n` record can come
  later if a proof wants one.
- It lives in `crates/elab/src/std/Vec/Vec.sw`, loaded only when a program uses it.
- Day 4: the grid becomes `{ height: Nat, width: Nat, rows: Vec (Vec Bool width) height }`,
  rectangular by its type. `parseGrid: List Text -> Maybe Grid` refuses ragged input. The spec
  describes the grid by positions: a roll is accessible when fewer than 4 of the positions
  next to it hold rolls, where "next to" is `Nat.absDiff` at most 1 in each direction. The
  theorems become `solvePart1 grid = part1Spec grid` with **no precondition**. Most of the
  existing part 1 proof carries over: about 350 lines in all, plus about 150 lines of `Vec`
  library.

## 1. Background: Stitchwort today

- **Data types have parameters but no indices** (`docs/core.md`, the table at the top:
  "Parameters but no indices. Equality is the only built-in indexed type"). The surface syntax
  agrees: `type Vec (a: Type): Nat -> Type = …` is a parse error. A type that depends on a
  number is computed by a definition instead (`def Shape: Nat -> Type`,
  `examples/accept/number-patterns.sw`).
- **Records** (`docs/proposals/records.md`, stage 1 built) are data types with one constructor.
  A field's type may mention earlier fields (`{ items: List Nat, sorted: IsSorted items }`).
  Proof fields are erased at run time, and in JavaScript a record is a plain object. The
  boundary checks a proof field on input with a decision procedure (records.md §11).
- **`auto` arguments** (`[auto ok: i < List.length xs]`, docs/syntax.md) are filled in by a
  decision procedure when the proposition is closed, as with `List.getOrConcatReplicate`'s
  `[auto hk: k != 0]`.
- **Lists** have the toolkit (`map`, `zipWith3`, `sumBy`, `getOr`, `transpose`, …) and, since
  day 6, lemmas about them by index (`List.getOrMap`, `List.getOrZipWith3`, `List.mapGetOr`,
  `List.sumByGetOr`).
- **Day 4** (`aoc/src/Aoc/Year2025/Day04/`) is `Grid = List (List Nat)` of 0/1. Part 1 is proved for
  every rectangular grid (`part1Correct lines w rect`), the rectangle being a precondition on
  `List Text`. Part 2 isn't proved (its approach, D123, is parked).

## 2. What day 4 needs

- A grid that is rectangular by construction, so the theorem needs no precondition and no
  `getOr` defaults inside the grid.
- Operations: `map`, `zipWith` and `zipWith3` of equal lengths, `replicate`, `sumBy`/`count`,
  `toList`, building from a list of unknown length, and `get` by an index in range (the spec and
  proofs; the program walks rows and never indexes).
- A way for parsing to return a grid whose size is known only at run time.

## 3. How other systems do it

| System | Type | Representation | Index |
|---|---|---|---|
| Lean 4 core | `Vector α n` | `structure` with `toArray : Array α` and `size_toArray : toArray.size = n` | `Fin n`, or `Nat` with a proof `i < n` (`v[i]` via `GetElem`); `getD` with a default |
| Mathlib | `List.Vector α n` | a `def` on a list with its length | `get (l : Vector α n) (i : Fin n)` |
| Agda stdlib | `Vec A n` | indexed data type: `[] : Vec A zero`, `_∷_ : (x : A) (xs : Vec A n) → Vec A (suc n)` | `lookup : Vec A n → Fin n → A` |
| Idris 2 base | `Vect len elem` | indexed data type (`Nil : Vect Z elem`, `(::)`) | `index : Fin len -> Vect len elem -> elem` |
| Haskell `vector-sized` | `Vector n a` | an ordinary `Data.Vector` tagged with a type-level `n` (a `newtype`, **unverified**: the page shows a type synonym for the generic version) | `index :: Vector n a -> Finite n -> a`; `fromList :: KnownNat n => [a] -> Maybe (Vector n a)`; `withSizedList` for an unknown size |

The pattern: the proof assistants with a fast runtime (Lean) use **data plus a length proof**, so
the run-time form is the ordinary array or list and the lemmas come from that type. Agda and
Idris use **indexed families**, which make structural recursion on the vector natural. Idris 2
can erase the length with quantity 0, but `Vect`'s declaration doesn't annotate it. Haskell
uses **a phantom size** on an ordinary vector, and `Maybe` or a continuation for a size known
only at run time. The last is the same problem day 4's parser has.

## 4. Representation options

### A. A record: a list and its length (recommended)

```
type Vec (a: Type) (n: Nat) = { list: List a, len: List.length list = n }
```

- **Works today.** No kernel or elaborator change. A scratch file with this type, `Vec.map`
  (its `len` from `List.lengthMap`) and a dependent grid record checked and ran.
- **Proofs.** Each operation is the list operation plus a length lemma. Facts about the
  elements are facts about `v.list`, so day 6's index lemmas apply as they are. The cost: two
  vectors with the same list and different proofs are equal only by proof irrelevance
  (docs/proposals/proof-irrelevance.md); a lemma `Vec.ext: v.list = w.list -> v = w` covers
  it.
- **Performance.** At run time a `Vec` is a record holding the list, because the proof is erased.
  There is one extra object per vector (per row in day 4, 140 of them), and no extra steps per
  element.
- **JavaScript.** A record is a plain object `{ list: [...] }`, and the proof isn't there. On
  the way in, the boundary checks `len` with the `Nat` decision procedure (records.md §11).
- **Hashing.** A new data type and new definitions, so the hash snapshot only gains lines.

### B. A computed type: nested pairs

```
def Vec (a: Type): Nat -> Type
  | 0      => Unit
  | Succ n => Pair a (Vec a n)
```

This works today too (the scratch file checked it with `Std.Builtin.UnitType`). But a grid's
size is a variable, so `Vec a n` doesn't compute, and every function must recurse on `n`, not on
the data. There are no list lemmas to reuse. In JavaScript it is nested pair objects. **Not
recommended.**

### C. An indexed data type (Agda, Idris)

```
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)
```

This is the textbook form. Matching on `VCons` teaches the checker that `n = Succ m`. It needs
indexed data types in the kernel: the eliminator's motive over indices, the positivity and
`Prop`-elimination checks with indices (DESIGN.md §6 already anticipates "appears in the result
type's indices"), and unification of indices in the elaborator's pattern compiler. That is a
milestone of its own, in the trusted core. It is worth having eventually (D133), but not for
day 4.

## 5. Indexing

Two ways, both expressible today:

- **`(i: Nat) [auto ok: i < n]`**: `Vec.get v i`, the proof found by `auto` for a literal index,
  or passed by name in a proof. This matches Lean's `v[i]` with a bound proof. It needs no new
  type, and indices stay plain numbers, so `List.getOr` lemmas apply directly
  (`Vec.get v i = List.getOr d i v.list` for any `d`).
- **`Fin n`**, a record `{ val: Nat, ok: val < n }`: Agda, Idris, Mathlib and `vector-sized`
  use it. It is useful for "all indices" statements and for counting positions
  (`List.range n` as `Vec (Fin n) n`). Day 4 doesn't need it: the spec counts over `List.range`.

Recommendation: the `Nat` and `auto` form now, and `Fin` when a use appears (D127).

## 6. The library file

`crates/elab/src/std/Vec/Vec.sw`, namespace `Vec`, loaded only when used (lazy library files;
`crates/elab/src/library.rs` lists the files). It holds:

- `Vec.fromList (xs: List a): Vec a (List.length xs)`, and
  `Vec.ofList (n: Nat) (xs: List a): Maybe (Vec a n)` (`Nothing` if the length differs).
- `Vec.toList`, which is the field.
- `Vec.replicate (n) (x): Vec a n`, `Vec.map`, `Vec.zipWith`, `Vec.zipWith3`, `Vec.sumBy`,
  `Vec.count`.
- `Vec.get v i [auto ok: i < n]`.
- Lemmas: `Vec.ext`, `Vec.getMap`, `Vec.getZipWith3`, `Vec.getReplicate`, and
  `Vec.sumByGet` (a sum is the sum over indices). Each is a few lines from the list lemma.

About 150 lines. Hash snapshot: additions only.

**Grids of a size known at run time.** A dependent record packs the size with the data:

```
type Grid = { height: Nat, width: Nat, rows: Vec (Vec Bool width) height }

def parseGrid (lines: List Text): Maybe Grid :=
  let width := (lines.headOr "").length
  lines.map parseLine |> traverse (Vec.ofList width) |> Maybe.map (rows => { height = lines.length, width = width, rows = Vec.fromList rows })
```

(The sketch needs a `List.traverse` for `Maybe`, or an explicit fold, and a cast from
`Vec … (List.length rows)` to `Vec … lines.length`. Details are for implementation.) `main`
prints an error for `Nothing`. This is the Haskell `fromList … -> Maybe` pattern. Whether
`Grid` is day 4's own type or a library `Matrix` is D129.

## 7. Day 4 over `Vec`

### The spec, by positions (D125)

```
-- The cell in row r, column c holds a roll; off the grid, it doesn't.
def roll (grid: Grid) (r: Nat) (c: Nat): Bool := …   -- r < height && c < width && the cell

-- Two different positions are next to each other when each coordinate
-- differs by at most 1 (the "eight adjacent positions").
def adjacent (r: Nat) (c: Nat) (r2: Nat) (c2: Nat): Bool :=
  Nat.absDiff r r2 <= 1 && Nat.absDiff c c2 <= 1 && not (r == r2 && c == c2)

def neighbours (grid) (r) (c): Nat :=
  positions grid |> .count ((r2, c2) => adjacent r c r2 c2 && roll grid r2 c2)

def accessible (grid) (r) (c): Bool := roll grid r c && neighbours grid r c < 4

def part1Spec (grid: Grid): Nat := positions grid |> .count ((r, c) => accessible grid r c)
```

`positions grid` is every `(r, c)` with `r < height`, `c < width`. This states "fewer than four
rolls of paper in the eight adjacent positions" without a border trick or `r - 1`. For part 2, a
set of rolls is a function `Nat -> Nat -> Bool` (or a predicate), which is what the core
argument (D123, parked) needs: "stable", "the largest stable set", "removing accessible rolls
never touches the core".

### The theorems (D124)

```
theorem part1Correct (grid: Grid): solvePart1 grid = part1Spec grid
theorem part2Correct (grid: Grid): solvePart2 grid = part2Spec grid     -- later, D123
theorem parseGridCells (lines) (grid) (h: parseGrid lines = Just grid) (r c):
  roll grid r c = (r < lines.length && (List.getOr "" r lines).toList.getOr ' ' c == '@')
```

`parseGrid`'s claim is short. With `parseLine` a `map`, it is `List.getOrMap` and `Vec.getMap`.

### What carries over from today's part 1 proof

- The program keeps its shape. `roundFrom`, `peelRow` and `peelCells` run on `rows.list` and each
  row's `list` (or on `Vec` versions that are the list functions plus a length lemma). The cell
  lemmas (`peelCellsAt`, `roundFromAt`, `colsAt`, `cellRound`; about 150 lines) carry over with
  `Bool.toNat` in place of 0/1 numbers. Their length bookkeeping (`Rows`, `rowsLength`,
  `lenCols`, about 40 lines) mostly disappears, because the lengths are in the types.
- `parseCharBit`, `borderedBit` and the rectangle precondition go. A cell is a `Bool`, and the
  grid is rectangular by type.
- New: the position spec's neighbour count, a count over all positions with `adjacent`, equals
  the window's eight cells. This is a reindexing lemma: only positions within 1 in each
  direction count, and on the grid's edge the missing ones are off the grid. About 100 to 150
  lines, the main new work.
- Total for part 1: about 350 lines of proof (today: 264), plus about 150 lines of `Vec` library
  and about 30 for `parseGrid`.

### Speed

The program does the same steps on the same lists. The records add one object per row, and the
`Maybe` parse adds one pass. `dev/t aoc` should stay at about 5 s; this needs measuring once
built.

## 8. Decisions wanted

- **D126. Representation.** (A) a record of a list and its length proof (recommended: works
  today, list lemmas carry over, same run-time cost); (B) nested pairs computed from `n`; (C)
  an indexed data type, which needs kernel indices.
- **D127. Indexing.** `Vec.get v (i: Nat) [auto ok: i < n]` now (recommended), or a `Fin n`
  record from the start.
- **D128. Name and home.** `Vec`, in `std/Vec/Vec.sw`, namespace `Vec` (recommended). Or
  `Vector`, the name Lean uses.
- **D129. The grid type.** Day 4's own `Grid` record `{ height, width, rows }`, returned as
  `Maybe Grid` by `parseGrid` (recommended), or a library `Matrix` for grids in general (days
  7 and others have grids too).
- **D130. Cells.** `Bool` (a roll or not; recommended, matching the spec), or keep `Nat` 0/1,
  as the sums use them now.
- **D131. Neighbours in the spec.** Count the positions with `Nat.absDiff` at most 1 in each
  direction, other than the cell itself (recommended, the puzzle's "eight adjacent
  positions"), or list the eight offsets as today.
- **D132. Ragged input.** `parseGrid` returns `Nothing` and `main` reports an error
  (recommended), or pads short lines with floor.
- **D133. Indexed data types.** Record "indexed families in the kernel" as a later milestone
  (Agda/Idris-style `Vec`, `Fin`), not needed for day 4. Yes or no.

## As decided

SW-179, 20 October 2026. Matt's decisions (D191): D126 by measurement between (A) and (C),
C by default; D127 `Fin n` plus `getLt` with an `auto` bound; D128 `std/Vec/Vec.sw`,
namespace `Vec`, loaded on use; D134 no external review. Indexed data types are in the
language since SW-178 (docs/syntax.md "Indexed data types").

### Measurements (D126)

Three scratch programs did the same work on a 136 × 136 grid of `Nat`, the size of day 4's
input (136 wide, 135 rows): **L**, plain `List (List Nat)`; **A**, the record
`{ list: List a, len: List.length list = n }` with each operation the list one plus its
length proof; **C**, the indexed data type. Each parses the grid from a `List (List Nat)`
(`ofList` per row, then a `traverse`), runs 20 rounds of one operation over every row, and
sums the result. Times are `stitchwort run` (release build, the interpreter), best of 3,
with the size, round count and operation read from standard input so that checking can't
compute the answer. The per-round figure is (time for 20 rounds − time for 0 rounds) / 20.

| Operation (every row of the grid) | L | A | C |
|---|---|---|---|
| 0 rounds: check, parse, one sum (total) | 0.20 s | 0.30 s | 0.26 s |
| `map` | 43 ms | 44 ms | 48 ms |
| `zipWith` | 57 ms | (not comparable)¹ | 58 ms |
| `zipWith3` | 70 ms | 71 ms | 75 ms |
| `replicate` | 9.5 ms | 9.5 ms | 8.5 ms |
| `sumBy` (row sums, then the total) | 26 ms | 26 ms | 28 ms |
| `toList` then `fromList`, linear² | — | 0 ms³ | 22 ms |
| `toList`, `fromList` and a sum, with the quadratic `fromList`⁴ | — | 33 ms³ | 487 ms |

1. A's `zipWith` was written with `List.zipWith3`; the same work as its `zipWith3` row.
2. C: `Vec.fromListN w (Vec.toList row) (Vec.lengthToList row)`, which stores numbers
   already computed (indexed-families.md §8.1).
3. In A both conversions are the field itself (`v.list`, `{ list = xs, len = rfl }`),
   so they cost nothing; 33 ms is the sum.
4. `fromList: (xs: List a) -> Vec a (List.length xs)` by plain recursion, so each `VCons`
   stores `List.length` of the rest. About 10 times the linear version's 22 + 28 ms at this
   size, and growing with the square of the row length. The library has only the linear
   one.

With `--js` (Node), 20 rounds of `zipWith3` took 0.27-0.29 s in all three: the difference
is below noise. End to end, a sketch of day 4 part 1 over `Vec` (below) took 0.56 s on the
real input against 0.53 s for the same program over lists, both including checking, and
both give 1397.

So C costs about 5-10% more per operation than lists and A, from the stored length in each
`VCons`, and a linear conversion to or from a list costs about one `map`. A day 4 program
converts once (parsing), so the difference is a few hundredths of a second.

A side finding, **unverified as to cause**: the first version of the A program had the
grid size and input as closed definitions (`def SIZE: Nat := 136`). Checking its `main`
then ran out of evaluation steps after 3 min 47 s (`E-RESOURCE`), while C's program in the
same form checked and ran in 5 s. Reading the size from standard input avoided it. I
suspect the checker evaluating the closed `parse SIZE SIZE input` through A's `Nat.decEq`
and length proofs, but didn't confirm it.

### Proof ergonomics

- **C.** Each lemma is an induction on the vector of two to four lines, with no arm for
  impossible cases: `Vec.getMap` is `rfl` and the induction hypothesis. Lengths never appear
  as proof terms. Facts about lists come over through the `toList` lemmas
  (`Vec.toListMap`, `Vec.toListZipWith3`, `Vec.sumByToList`, …) and `Vec.getToList`
  (`get` is `List.getOr` at `Fin.toNat i`), so day 6's index lemmas still apply.
  `Vec.ext` is three lines.
- **A.** `get` facts are the list facts directly, but every operation builds its length
  proof by hand (`zipWith3`'s is `Eq.trans (List.lengthZipWith3 f … (Eq.trans v.len
  (Eq.sym u.len)) …) u.len`), record literals inside lambdas need type annotations
  (`E-CANNOT-INFER`), and two vectors with the same list are equal only through proof
  irrelevance or an extensionality lemma.

**Choice: C.** It costs a few per cent at run time, and makes the library and its proofs
shorter.

### The library

`std/Fin/Fin.sw` (namespace `Fin`, 36 lines) and `std/Vec/Vec.sw` (namespace `Vec`, about
200 lines), both in `LIBRARY_FILES` and loaded on use. `Vec.sw` uses `Fin` and
`List.getOr`, so it loads `Fin/Fin.sw` and `List/Index.sw`.

```
type Fin: Nat -> Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)
```

| Group | Names |
|---|---|
| `Fin` | `Fin.toNat`, `Fin.ofNatLt n i h`, `Fin.ofNat i [auto ok: i < n]`; lemmas `Fin.toNatLt`, `Fin.toNatOfNatLt` |
| Shape | `Vec.length` (the index), `Vec.head`, `Vec.tail` (on `Vec a (Succ n)`), `Vec.headOr d` |
| Building | `Vec.replicate n x`, `Vec.map`, `Vec.zipWith`, `Vec.zipWith3` |
| Folding | `Vec.foldLeft`, `Vec.sum`, `Vec.sumBy` |
| Lists | `Vec.toList`; `Vec.fromListN n xs (ok: List.length xs = n)` (linear); `Vec.fromList xs: Vec a (List.length xs)`; `Vec.ofList n xs: Maybe (Vec a n)`; `Vec.traverseMaybe` |
| Indexing | `Vec.get v (i: Fin n)`; `Vec.getLt v (i: Nat) [auto ok: i < n]` |
| Lemmas, `toList` | `lengthToList`, `toListFromListN`, `toListFromList`, `ofListToList` (what `ofList` accepts is its list), `toListReplicate`, `toListMap`, `toListZipWith`, `toListZipWith3`, `foldLeftToList`, `sumByToList`, `sumToList` |
| Lemmas, `get` | `getToList` (`List.getOr d (Fin.toNat i) (toList v) = get v i`), `getReplicate`, `getMap`, `getZipWith`, `getZipWith3`, `ext` |

Tests are in both files; `examples/accept/vec-library.sw` parses a grid, proves
`flip`'s cells through `Vec.getMap`, and a `sumBy` over a `map` through the `toList`
lemmas.

Changes from §6: `Fin` came first (D127), so `get` takes a `Fin` and `getLt` builds one;
`fromList` is the linear `fromListN` at the list's length; `Vec.traverseMaybe` replaces the
"traverse for `Maybe`" the parser sketch needed. §6's `Vec.ext` (vectors with equal lists
are equal) belonged to A; here `Vec.ext` is equality by position. There's no `Vec.count`
yet (day 4 sums with `sumBy`). `==` isn't derived for indexed types yet, so tests compare
`toList`.

### Day 4 over this API

A sketch of part 1, checked and run on the real input (1397), not the port:

```
type Grid = { height: Nat, width: Nat, rows: Vec (Vec Cell width) height }

-- `Nothing` for ragged input.
def parseGrid (lines: List Text): Maybe Grid :=
  let width := (lines.headOr "").length
  Vec.fromList lines
    |> Vec.traverseMaybe (line => Vec.ofList width (parseLine line))
    |> Maybe.map (rows => ({ height = lines.length, width, rows }: Grid))

def Grid.rolls (grid: Grid): Nat := grid.rows.sumBy (row => row.sumBy Cell.count)

def Grid.round (grid: Grid): Grid :=
  let gap := Vec.replicate grid.width Floor
  { grid | rows = roundFrom gap gap grid.rows }

def roundFrom (gap above: Vec Cell w): Vec (Vec Cell w) h -> Vec (Vec Cell w) h
  | VNil           => VNil
  | VCons row rest => VCons (peelRow above row (rest.headOr gap)) (roundFrom gap row rest)

def peelRow (above row below: Vec Cell w): Vec Cell w :=
  peelCells 0 (Vec.zipWith3 (a r b => a.count + r.count + b.count) above row below) row

def peelCells (left: Nat): Vec Nat w -> Vec Cell w -> Vec Cell w
  | VNil, VNil => VNil
  | VCons here columns, VCons roll rolls =>
    let window := left + here + columns.headOr 0
    VCons (if roll == Roll && 5 <= window then Roll else Floor) (peelCells here columns rolls)

-- For the spec: a cell by `Nat` position; off the grid is no roll.
def Grid.roll (grid: Grid) (r: Nat) (c: Nat): Bool :=
  if hr: r < grid.height then
    if hc: c < grid.width then Vec.getLt (Vec.getLt grid.rows r [ok := hr]) c [ok := hc] == Roll
    else False
  else False
```

The program keeps today's shape: `roundFrom`, `peelRow` and `peelCells` are the list
versions with `VCons` for `Cons` and `Vec.headOr` for `List.headOr`, and `peelCells` no
longer needs a catch-all arm, since its two vectors have the same length. The proofs can
state cell facts with `Vec.get`/`Vec.getLt` and move between the grid and lists with
`Vec.getToList`, `Vec.toListZipWith3` and `Vec.sumByToList`; `parseGrid`'s claim goes
through `Vec.ofListToList`. Everything above exists in the library. Not there yet, and
for the port to add if it wants them: lemmas about `traverseMaybe` (each element of the
result is `f`'s `Just` of the input's), `Vec.headOr` of a `tail`, and a `Vec.count`.

### Pain points with families (feedback for SW-178)

- **A missing `Zero` arm isn't excused by an empty `Fin 0` in the next column.**
  `getReplicate: (n: Nat) -> (i: Fin n) -> …` with arms `Succ k, FZero` and
  `Succ k, FSucc i` is `E-NONEXHAUSTIVE` ("no arm matches `Zero`"), though `i: Fin 0` then
  has no values. syntax.md says an arm may be left out "when another argument then has no
  possible constructor"; it works when the left-out constructor is a family's (`get`'s
  `VNil`), not for `Nat`'s `Zero` here. The workaround matches only on the `Fin` and names
  its implicit field: `| _, FSucc [n := k] i => Vec.getReplicate x k i`.
- **The quadratic `fromList` is the natural definition** (§8.1 of the families note): 487
  ms against about 50 ms per grid at day 4's size. The library offers only the linear one,
  but a user writing their own will hit it.
- **No injectivity for free.** `Vec.ofListToList` needs `Just (VCons x w) = Just (VCons y
  ys)` taken apart, by `Eq.cong` with `Maybe.withDefault`, `Vec.head` and `Vec.tail`, as
  for plain data types; the unifier's injectivity is only for matching.
- **`==` isn't derived** for an indexed type, so tests compare `Vec.toList`.
- Not about families, met on the way: a record literal at the end of a `|>` pipe has no
  expected type and needs `({ … }: Grid)`; and `getLt`'s `auto` bound is stuck for a size
  known only at run time (as designed: pass a proof from `if h: …`).

## Sources

- Lean 4 core `Vector`: `src/Init/Data/Vector/Basic.lean` in leanprover/lean4 (`structure
  Vector (α : Type u) (n : Nat)` with `toArray` and `size_toArray`; `get` by `Fin n`;
  `GetElem` with `i < n`; `getD`).
- Mathlib: `Mathlib/Data/Vector/Defs.lean` (`def List.Vector (α : Type u) (n : ℕ)`,
  `get (l : Vector α n) (i : Fin n) : α`).
- Agda standard library: `src/Data/Vec/Base.agda` (`data Vec`, `lookup`).
- Idris 2: `libs/base/Data/Vect.idr` (`data Vect : (len : Nat) -> (elem : Type) -> Type`,
  `index : Fin len -> Vect len elem -> elem`).
- Haskell `vector-sized`: hackage.haskell.org/package/vector-sized, `Data.Vector.Sized`
  (`index`, `fromList`, `withSizedList`).
- Stitchwort: `docs/core.md` (no indices), `docs/proposals/records.md` (dependent fields,
  erasure, JS form, §11), `docs/syntax.md` (`auto`), DESIGN.md §6.
