# Plan: `Map`/`Set` lemmas for maps of sets, then 2024 day 9 part 2 proved

**Status:** draft 1, 7 November 2026. Ticket SW-745. This is a plan for lanes, written
read-only against `main` at `79047815d`. Nothing was built or run for it. It stops for
Matt's decisions ([§7](#7-decisions), D3070–D3071).

Labels: **[checked]** means read in the repository at the place given; **[inferred]** means
my reasoning from checked facts; **[unverified]** means believed but not confirmed.

## 0. Summary

**What you get.** 2024 day 9 part 2 proved equal to the puzzle's spec for every disk map.
It is one of the three 2024 parts still unproved (synthesis theme O,
`docs/research/aoc-friction-synthesis.md:377`). Along the way std gets a small "map from a
key to a set" vocabulary. Days 6, 9 and 23 of 2024 each build that kind of map by hand. Std
also gets the `List.findIndex` lemmas four days have asked for (SW-1531).

**The main finding.** The "list model" the ticket asks for is already in std. Since 23
October every `Map` operation has had a lemma giving its entries as a sorted list:
`Map.toListAlter`, `Map.toListAdjust`, `Map.toListInsert`, `Map.toListRemove` and
`Map.minToList` (`std/Map/Map.sw:421–502`). Every operation also has its key-by-key
lemmas: `Map.getAlter`/`getAlterOther` (`Map.sw:716–722`), `Map.getAdjust`/`getAdjustOther`
(`Map.sw:723–730`), `Set.containsInsertIff`/`containsRemoveOther` (`Set/Spec.sw:394`,
`:200`), `Set.minToList`/`containsMin`/`missingOfMinNone` (`Set/Spec.sw:89–138`). Most of
these existed when day 9 was written on 28 October; the `git log -S` dates are in §1. Day 9's
note asked for "specs of `Map.alter`, `Map.adjust`, `Set.insert`, `Set.remove` and
`Set.min`" (`aoc/NOTES-2024.md:2455–2458`), but what the proof really lacked was everything
else: the invariant, and the bridge from spans to the spec's blocks. The note says so itself
("Items 1 and 4 are most of the work", `NOTES-2024.md:2463`).

**Recommendation.** Use the key-by-key view, not the sorted list, as the model (§2). Add
about 120 lines to std: the map-of-sets functions and their lemmas, two `Set.min` facts, and
small `minBy`, `Option.filter` and `findIndex` lemmas. Then prove day 9 through an
in-between picture: a list of files with spans, drawn as a disk (§4). There are six lanes,
about 1,200 lines and 7 hours of lane time in all. Two of them can run side by side from
the start (§5).

## 1. What exists, and what doesn't

**The problem, plainly.** Day 9 part 2 keeps the free space in `FreeSpace = Map Nat (Set
Nat)`: for each length, the starts of the free runs of that length (`Day09.sw:121`). The
program adds runs with `Map.alter` and `Set.insert` (`Day09.sw:123–125`), takes them out
with `Map.adjust` and `Set.remove` (`:127`), and finds the leftmost run that fits by
scanning `free.toList` and taking each set's `min` (`:131–137`). To prove the program right,
you have to say what the map holds after each step. That needs one lemma per operation.

**What std has** [checked]:

| Operation | As a sorted list | Key by key | Added |
| --- | --- | --- | --- |
| `Map.alter` | `Map.toListAlter` (`Map.sw:434`) | `Map.getAlter`, `getAlterOther` (`:716`, `:719`) | 23 Oct (`bab03f79e`, `57bd67847`) |
| `Map.adjust` | `Map.toListAdjust` (`:438`) | `Map.getAdjust`, `getAdjustOther` (`:723`, `:726`) | 23 Oct |
| `Set.insert` | `Set.toListInsert` (`Set/Spec.sw:10`) | `containsInsert`, `containsInsertOther`, `containsInsertIff` (`Set.sw:115`, `Spec.sw:241`, `:394`) | 23 Oct |
| `Set.remove` | `Set.toListRemove` (`Spec.sw:14`) | `containsRemove`, `containsRemoveOther` (`:197`, `:200`) | 23 Oct |
| `Set.min` | `Set.minToList` (`:89`) | `containsMin` (`:99`), `missingOfMinNone` (`:138`) | 28 Oct (`54ff38c34`) |
| `Map.toList` membership | `Map.memToList` (`Map.sw:341`), `toListSorted` (`:331`) | | 23 Oct (`c216916c5`) |
| `List.minBy` | `List.minBySome`, `minByFirst` (`List/Lemmas.sw:1684`, `:1703`) | | 6 Nov (`8736db293`) |
| `List.find` on a range | `findRangeSome`, `findRangeNone`, `findRangeFirst` (`List/Lemmas.sw:1463–1490`) | | |

**What is missing** [checked by grep over `crates/elab/src/std`]:

1. **"The minimum is at most every member" for any `Set`.** It exists only as
   `Graph.minLeast`, specialised to `Set (Nat, s)` and comparing first components
   (`std/Graph/Search.sw:222`). Day 16 asked for the general one by name
   (`NOTES-2024.md:4985`).
2. **"A set with a member has a minimum."** It's the converse of `missingOfMinNone`. You
   can get it today in six lines, as day 23 does (`Day23/Proofs/Part2.sw:74–79`).
3. **`List.minBy … = None` means the list is empty**, and **`Option.filter … = None`**
   (only the `Some` case exists, `Option/Lemmas.sw:157`).
4. **`List.findIndex` has no lemmas at all** (`List/Toolkit.sw:741–748`; SW-1531). The
   spec's `Disk.fileStart` is a `findIndex` (`Spec.sw:56`).
5. **No map-of-sets vocabulary.** Each day writes `m.getOr key Set.empty |> .contains x`
   and its own insert lemma. Day 6 proved `lineAfterAdd` for its version
   (`Day06/Proofs/Sightlines.sw:22–33`). Day 9 would need the same for `alter`/`adjust`.

## 2. The model

**The problem.** A proof about `FreeSpace` has to state what the map holds, as something
that can be checked against the disk. There are three ways to say it.

**Design A: the sorted association list (`toList`).** State the invariant on
`free.toList`, rewrite each step with `Map.toListAlter`/`toListAdjust`, and reason about
`Map.Spec.alter` (`Map/Spec.sw:70`), a recursive list function, using sortedness. All the
lemmas exist. The catch is that every step needs a list induction with `Map.Spec.Ascending`
side conditions, and each value is itself a set whose `toList` is a list of `(k, ())`
pairs. AoC proofs almost never take this route. Across `aoc/src` and `games` I counted 23
uses of `Set.containsFromListIff`, 13 of `Set.memToList` and 9 of
`Set.containsInsertOther`, but `Map.toListInsertWith` only in the two "sum over every entry"
proofs (2024 day 11 `Counting.sw:37`, 2021 day 14 `Weights.sw:24`) [checked]. The list form
pays off when the proof folds over every entry. Day 9 doesn't.

**Design B: key by key (`get`/`contains`), with order facts only where order matters.**
State the invariant as "span `(length, start)` is in the map exactly when it is a gap of the
disk". Each step is then two existing rewrites (`getAlter` plus `containsInsertIff`).
`toList` appears only once, in `leftmostFit`, through `Map.memToList`, to say which entries
the scan sees. This is how days 6, 16 and 23 proved their maps and sets [checked: day 6
`Represents`, `Sightlines.sw:18–20`].

**Design C: B, plus a named map-of-sets layer in std.** Give "map from a key to a set" its
own three functions and their `↔` lemmas, so the program says `free.insertIn length start`
and the proof uses one lemma for each step instead of composing two.

**Recommendation: C.** B is the right model: it's what works in practice, and it keeps the
sorted list out of day 9. C costs about 60 more lines of std, makes day 9's program read in
its own terms, and turns day 6's `lineAfterAdd` into a std lemma. Lean's
`Std.TreeMap` and Mathlib's `Finmap` lean on the same key-by-key `get?_insert` /
`contains_alter` style for day-to-day proofs, and keep `toList` for folds [unverified:
from memory, not re-read]. Rust has no multimap in `std` (people write
`entry(k).or_default().insert(x)`); Guava's `SetMultimap` is the named-layer version. C rules
out nothing: anyone can still use `alter` directly.

**One semantic choice, which I made:** `removeIn` drops a key whose set becomes empty. With
that, two maps of sets holding the same pairs are equal (by `Map.ext` and `Set.ext`). That
is the end state worth having, and it costs `removeIn` one `alter` instead of one `adjust`.
Day 9's `leftmostFit` already ignores empty sets (their `min` is `None`), so nothing depends
on this either way.

## 3. The std lemmas

**The problem.** Without these, day 9's proof writes them itself, and days 6, 16 and 23
have already written some of them, or worked around their absence.

**The change.** These are exact statements, in std's style. A lane may adjust implicit
arguments where elaboration needs it.

### 3.1 Maps of sets (`std/Set/Set.sw` "Maps and sets" for the functions, `std/Set/Spec.sw` for the lemmas)

```stitchwort
--| Whether `item` is in the set at `key`.
def Map.containsIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Bool :=
  m.getOr key Set.empty |> .contains item

--| With `item` added to the set at `key`, which starts empty if there is none.
def Map.insertIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Map k (Set v) :=
  m.alter key (items => items.getOrElse Set.empty |> .insert item |> Some)

--| With `item` taken out of the set at `key`; a set left empty is dropped, so
--| maps holding the same pairs are equal.
def Map.removeIn [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v): Map k (Set v) :=
  m.alter key (items => items.map (.remove item) |> .filter (rest => !rest.isEmpty))

theorem Map.containsInEmpty [auto ord: Ord k] [auto itemOrd: Ord v] (key: k) (item: v):
    (Map.empty: Map k (Set v)).containsIn key item = False

theorem Map.containsInInsertInIff [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v):
    ((m.insertIn key item).containsIn otherKey otherItem = True) ↔ ((otherKey = key ∧ otherItem = item) ∨ m.containsIn otherKey otherItem = True)

theorem Map.containsInRemoveInIff [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v) (otherKey: k) (otherItem: v):
    ((m.removeIn key item).containsIn otherKey otherItem = True) ↔ (¬(otherKey = key ∧ otherItem = item) ∧ m.containsIn otherKey otherItem = True)

--| The entries `toList` walks hold exactly the pairs.
theorem Map.containsInToList [auto ord: Ord k] [auto itemOrd: Ord v] (m: Map k (Set v)) (key: k) (item: v):
    (m.containsIn key item = True) ↔ (∃ (items: Set v) => ((key, items) ∈ m.toList) ∧ (items.contains item = True))
```

The `Bool` equations for the same and the other pair (`containsInInsertIn`,
`containsInInsertInOther`, likewise for `removeIn`) come with them, as `Set` has both forms
(`Set/Spec.sw:197–249`, `:383–440`).

**Who would use them** [checked]:

- 2024 day 9: `FreeSpace.add`/`remove` (`Day09.sw:123–127`), ported to `insertIn`/`removeIn`.
- 2024 day 6: `Sightlines.add` (`Day06.sw:110–115`) builds `byRow`/`byColumn` with
  `insert`+`getOr`, and `lineAfterAdd` (`Day06/Proofs/Sightlines.sw:22–33`) is
  `containsInInsertIn` in `Bool` form. The `Represents` reads (`:18–20`) are `containsIn`.
- 2024 day 23: `Links` is a `Map Computer (Set Computer)` (`Day23.sw:65`), read with
  `getOr computer Set.empty` (`:74`). Its proofs could read it with `containsIn`; it's
  built by `groupBy`, so `insertIn` doesn't apply.

That makes three days. No 2020, 2021 or 2025 day has a `Map _ (Set _)` [checked by grep].

### 3.2 `Set.min` (`std/Set/Spec.sw`, after `containsMin`)

```stitchwort
--| The smallest key is at most every key of the set.
theorem Set.minLeast [auto ord: Ord k] (s: Set k) (least: k) (found: s.min = Some least) (key: k) (there: s.contains key = True): least <= key

--| A set holding a key has a smallest one.
theorem Set.minOfContains [auto ord: Ord k] (s: Set k) (key: k) (there: s.contains key = True): ∃ (least: k) => s.min = Some least
```

`minLeast` is `Graph.minLeast`'s proof (`Graph/Search.sw:222–237`) without the pair:
`Map.Spec.keysAbove` and then `ord.lessEqOf`. For `Set Nat`, `<=` is Nat's `≤` (Nat's `Ord`
has `lessEqOf = Nat.leOfCompare`, `core/Ord.sw:75`) [checked], so day 9 can use it directly.

**Who would use them:** 2024 day 9 (`Day09.sw:134`, `entry.snd.min`). Day 16 asked for
`minLeast` (`NOTES-2024.md:4985`) and got the pair version in `Graph` (`Graph/Search.sw:222`),
which serves 2021 day 15, 2024 day 16 and `Aoc.Common.GridGraph`. Restating `Graph.minLeast`
on top of `Set.minLeast` is optional, since it still needs "pair at most implies first
component at most". `minOfContains`: day 9; day 23's `noneHeld` (`Day23/Proofs/Part2.sw:74`)
is already `Set.missingOfMinNone`, which exists. That's a one-line cleanup, a finding below.
So there is one direct user, plus `Graph`.

### 3.3 Small list and option lemmas

```stitchwort
--| `minBy` finds nothing only in an empty list.
theorem List.minByNone [auto ord: Ord b] (xs: List a) (f: a → b) (found: xs.minBy f = None): xs = []

--| What `filter` drops: nothing, or something that failed the test.
theorem Option.filterEqNone: (x: Option a) → (p: a → Bool) → Option.filter x p = None → (x = None) ∨ (∃ (v: a) => (x = Some v) ∧ (p v = False))
```

Users: day 9's `leftmostFit` (`Day09.sw:136–137`). Each is a few lines, and they belong
beside `minBySome` (`List/Lemmas.sw:1684`) and `filterEqSome` (`Option/Lemmas.sw:157`).

### 3.4 `List.findIndex` (absorbs SW-1531; `std/List/Lemmas.sw`, near `findRangeSome`)

```stitchwort
--| What `findIndexFrom` finds passes, and nothing before it does.
theorem List.findIndexFromSome (p: a → Bool): (start: Nat) → (xs: List a) → (index: Nat) → List.findIndexFrom start p xs = Some index →
    (start ≤ index) ∧ (∃ (x: a) => (xs.get (index - start) = Some x) ∧ (p x = True))
      ∧ ((earlier: Nat) → start ≤ earlier → earlier < index → (y: a) → xs.get (earlier - start) = Some y → p y = False)

theorem List.findIndexSome (xs: List a) (p: a → Bool) (index: Nat) (found: xs.findIndex p = Some index):
    (∃ (x: a) => (xs.get index = Some x) ∧ (p x = True)) ∧ ((earlier: Nat) → earlier < index → (y: a) → xs.get earlier = Some y → p y = False)

theorem List.findIndexNone (xs: List a) (p: a → Bool) (found: xs.findIndex p = None) (x: a) (member: x ∈ xs): p x = False

--| The first index that passes is what `findIndex` finds.
theorem List.findIndexOf (xs: List a) (p: a → Bool) (index: Nat) (x: a) (at: xs.get index = Some x) (passes: p x = True)
    (before: (earlier: Nat) → earlier < index → (y: a) → xs.get earlier = Some y → p y = False): xs.findIndex p = Some index
```

The `From` form carries the induction, since `findIndex` is `findIndexFrom 0`
(`Toolkit.sw:748`) and a cons step moves the start. 2020 day 15's note hit exactly that
(`NOTES-2020.md:4164–4166`).

**Users** [checked]: 2024 day 9's spec (`Spec.sw:56`); 2021 day 18 (`Day18.sw:157`, whose
`findUnreducedNone` in `Proofs/Parse.sw:23` is a `findIndexFrom`-none lemma written by hand);
2025 day 7 (`Day07.sw:78`); and 2020 day 15, whose spec avoided `findIndex` for want of them
(`NOTES-2020.md:4164`). That's four days.

**What it should do, and how we'd know.** Day 9's proof uses no `Map.toList`/`Map.Spec`
lemma except `Map.containsInToList`. Day 6's `lineAfterAdd` can be deleted for a std lemma
(an optional follow-up). `stitchwort audit Std.Set` and `Std.List` stay clean.

## 4. Day 9 part 2: what the proof needs beyond std

**The problem.** The program works on spans (a file is `{ id, span = { start, length } }`;
free space is the map). The spec works on blocks: it finds a file with `findIndex`, measures
it with `count`, looks for room with `List.range 0 start |> .find (… freeAt …)`, and writes
the result with `mapWithIndex` (`Spec.sw:56–80`). The proof has to join the two. Day 9's
note lists four gaps (`NOTES-2024.md:2454–2463`). This plan closes them with three
in-between definitions and four groups of lemmas.

### 4.1 Three definitions (day 9's `Proofs/`, a new `Proofs/Disk.sw`)

```stitchwort
def Span.end (span: Span): Nat := span.start + span.length
def Span.covers (span: Span) (position: Nat): Bool := span.start <= position && position < span.end

--| The block at `position`; free past the end.
def Disk.at (disk: Disk) (position: Nat): Block := disk.blocks.getOr position Free

--| `size` blocks with each file's blocks where its span says. The files' spans don't overlap.
def drawFiles (size: Nat) (files: List File): Disk :=
  { blocks = List.range 0 size |> .map (position =>
      files.find (file => file.span.covers position) |> .map (file => FileBlock file.id) |> .getOrElse Free) }

--| `span` is a whole gap: not empty, all free, with the disk's start or a file block
--| before it and a file block after it.
def Disk.Gap (disk: Disk) (span: Span): Prop :=
  0 < span.length
    ∧ ((position: Nat) → span.covers position = True → disk.at position = Free)
    ∧ (span.start = 0 ∨ (disk.at (span.start - 1)).isFile = True)
    ∧ (disk.at span.end).isFile = True
```

`drawFiles` is the bridge: the program's state is a list of files, and the spec's disk at
each step is `drawFiles size` of it. Everything the spec computes by index (`findIndex`,
`count`, `freeAt`, `mapWithIndex`) is read off `Disk.at`, one position at a time, with the
existing `getOr` lemmas (`List.getOrMapRange`, `getOrMapWithIndex`, `extGetOr`;
`List/Index*.sw`).

### 4.2 The four groups

1. **`FreeSpace` against gaps** (needs §3.1–3.3). `FreeSpace.has free span :=
   free.containsIn span.length span.start`. The lemmas are `hasAdd`, `hasRemove`, `hasOf`,
   and `leftmostFit`'s spec in two halves:
   - `leftmostFitSome`: what's found is in the map, fits, starts before `before`, and starts
     at or before every other span in the map that fits;
   - `leftmostFitNone`: every span in the map that fits starts at or after `before`.

   This is `Map.containsInToList` + `List.memFilterMap` + `Set.minLeast` +
   `List.minBySome`/`minByNone` + `Option.filterEqSome`/`filterEqNone`.
2. **Drawing and the checksum.** `drawFiles` is pointwise (`Disk.at (drawFiles size files)
   p` is the covering file's block). The checksum of a drawing of non-overlapping files is
   the sum of `File.checksum` over them. Day 9 already has the one-file case
   (`fileChecksumCorrect`, `Proofs/Part2.sw:129`), and this closes gap 3.
3. **The spec's move, on a drawing** (gap 4, the hard one). Take a file of positive length,
   drawn where its span says, with no other file over it. Then:
   - `fileStart` finds its start (`List.findIndexOf`), and `count` is its length;
   - the leftmost free window `find` returns is the start of the leftmost gap before the
     file that is long enough. The key step: a leftmost free window can't have a free block
     just before it, so it starts a gap. Conversely, any long-enough gap holds a window at
     its start;
   - the `mapWithIndex` rewrite is `drawFiles` with the file's start changed.

   Stated as two lemmas whose hypotheses are exactly what `leftmostFitSome`/`None` give:

   ```stitchwort
   theorem moveWholeFileGap (size: Nat) (files: List File) (apart: Apart size files) (file: File) (member: file ∈ files)
       (positive: 0 < file.span.length) (gap: Span) (isGap: (drawFiles size files).Gap gap) (fits: file.span.length ≤ gap.length)
       (before: gap.start < file.span.start)
       (leftmost: (other: Span) → (drawFiles size files).Gap other → file.span.length ≤ other.length → other.start < file.span.start → gap.start ≤ other.start):
       (drawFiles size files).moveWholeFile file.id = drawFiles size (files.moveTo file.id gap.start)

   theorem moveWholeFileNoGap (size: Nat) (files: List File) (apart: Apart size files) (file: File) (member: file ∈ files)
       (positive: 0 < file.span.length)
       (none: (other: Span) → (drawFiles size files).Gap other → file.span.length ≤ other.length → file.span.start ≤ other.start):
       (drawFiles size files).moveWholeFile file.id = drawFiles size files
   ```

   `Apart size files` means distinct ids, spans that don't overlap, and every span within
   `size`. `files.moveTo id start` changes one file's start.
4. **The invariant through the fold** (gap 1). It needs `Tracks free disk bound := (span:
   Span) → span.start < bound → (free.has span = True ↔ disk.Gap span)`, where `bound` is
   the start of the next file of positive length still to move. It needs three things:
   - **at the start:** `FreeSpace.of (joinTouching layout.snd)` tracks the drawing of the
     unmoved files. This needs `joinTouching`'s spec (its spans are the disk's gaps) and
     `layoutFrom` against `blocksFrom` position by position (`layoutBlocks`,
     `Part2.sw:90`, has the flattened form);
   - **one step:** a move keeps `Tracks`, with the remainder `{ start + length, length -
     length }` as the new gap and the vacated blocks at or past the new bound;
   - **the fold:** `List.mapAccumLeft` over `layout.fst.reverse` against the spec's
     `foldLeft` over `List.range 0 fileCount |> .reverse`. That includes `fileCount = (lengths.length + 1) / 2` being the layout's
     file count. Std has `mapAccumLeftList` but no invariant form, so the lane writes a
     small `List.mapAccumLeftInvariant` and moves it to std if it's generic (D2831).

   The final theorem is `part2Correct (diskMap: DiskMap): solvePart2 diskMap = part2 diskMap`.

**Zero-length files** need care in every group. A file of length 0 has no blocks, so the
spec's `fileStart` is `None` and it never moves (`Spec.sw:67–68`). The program "moves" it,
removing and re-adding the same span, so the map doesn't change. But `joinTouching` merges
the two runs on either side of it into one gap that straddles its position. That is why
`bound` is the next file of *positive* length [inferred]. The tests cover these cases
(`NOTES-2024.md:2398–2402`), but nothing yet proves the program agrees with the spec on
every one. If a lane finds a counterexample, the program is fixed, not the spec.

**What it should do, and how we'd know.** `part2Correct` checks, and
`task audit:touched -- Aoc.Year2024.Day09` reports no `✗`. Day 9's `Proofs/Part2.sw`
header (`:1–4`) and the note's "Not proved" paragraph (`NOTES-2024.md:2454`) are
rewritten. The spec is unchanged: it's the puzzle's wording, and changing it to spans would
weaken what's proved.

**Designs considered for the whole proof.**

- **(i) Direct.** Relate the map to the spec's block list with no in-between picture. Every
  step would be index arithmetic over `mapWithIndex`, all in one place. Day 9's note
  estimated ~1,000 lines this way.
- **(ii) Through `drawFiles` and `Disk.Gap`** (recommended). The block arithmetic is in group
  3 only, behind two lemmas whose hypotheses match `leftmostFit`'s spec. Groups 1, 2 and 4
  never look at blocks by index, so the stages can run in parallel against fixed statements.
- **(iii) Change the program** to a single `Set (Nat, Nat)` of (length, start) pairs and
  drop the map. This saves the map-of-sets layer (cheap after §3.1) and nothing else. I
  rejected it.

## 5. Stages

Each stage is one lane. Estimates are lane working time; lines are new proof or std lines.
Std lanes don't touch std core (Int, Nat, Text, Char, Bool) or change an existing
definition, so extract's `bound_to_the_prelude` tests aren't needed [inferred: no native
binds a `Set`, `Map`, `List.findIndex` or `Option` lemma; the natives are by content hash in
`crates/rt/src/natives.rs`]. Every std stage commits the regenerated prelude snapshot.

Order: **S1 ∥ S3**, then **S2 ∥ S4**, then **S5**, then **S6**.

### S1. Std: maps of sets, `Set.min`, `minBy`, `Option.filter`, `findIndex` (Sonnet, 60 min, ~130 lines)

Absorbs SW-1531. Brief:

> Add to std the definitions and lemmas in `docs/proposals/map-set-list-model.md` §3: the
> map-of-sets functions `Map.containsIn`, `Map.insertIn`, `Map.removeIn` in
> `std/Set/Set.sw` ("Maps and sets"), with their `↔` lemmas and same/other `Bool` equations
> in `std/Set/Spec.sw` (§3.1); `Set.minLeast` and `Set.minOfContains` after
> `Set.containsMin` (§3.2; `Graph.minLeast`, `std/Graph/Search.sw:222`, shows the proof);
> `List.minByNone` and `Option.filterEqNone` (§3.3); and the `List.findIndex` lemmas (§3.4,
> SW-1531), the `From` form first. Keep the statements as written unless elaboration needs
> an implicit changed, and say so if it does. Each definition gets a full API doc and a
> `test`. Read `docs/proving-guide.md` first. Tests: `task test:lane AREA=std`; `task
> audit:touched -- Std.Set` and `-- Std.List`; `task snap:hashes` (no NAME, as for std
> changes) and commit the regenerated prelude snapshot (additions only); `task test:one --
> -E 'binary(hash_stability)'`. Expected: 60 min.

### S2. Day 9: `FreeSpace` on `insertIn`/`removeIn`, and `leftmostFit`'s spec (Sonnet, 60 min, ~180 lines)

After S1. Brief:

> In 2024 day 9 (`aoc/src/Aoc/Year2024/Day09/`), port `FreeSpace.add`/`remove` to std's
> `Map.insertIn`/`removeIn` (keep `add` skipping length 0). Then, in a new
> `Proofs/FreeSpace.sw`, prove group 1 of `docs/proposals/map-set-list-model.md` §4.2:
> `FreeSpace.has`, `hasAdd`, `hasRemove`, `hasOf`, `leftmostFitSome` and `leftmostFitNone`,
> with the statements given there. Use only the key-by-key lemmas and
> `Map.containsInToList`, not `Map.Spec`. The program's answers must not change. Tests: `cd
> aoc && stitchwort test Aoc.Year2024.Day09` (32 tests, about 2 s); `task audit:touched --
> Aoc.Year2024.Day09`. Expected: 60 min.

### S3. Day 9: `drawFiles`, `Apart`, and the checksum of a drawing (Sonnet, 60 min, ~150 lines)

Independent of S1, so it can start with it. Brief:

> In 2024 day 9's proofs, add `Proofs/Disk.sw` with the definitions of
> `docs/proposals/map-set-list-model.md` §4.1 (`Span.end`, `Span.covers`, `Disk.at`,
> `drawFiles`, `Disk.Gap`) and `Apart size files` (distinct ids, spans that don't overlap,
> each within `size`). Prove `drawFiles` pointwise (the block at `p` is the covering file's,
> or `Free`), and group 2: `filesystemChecksum (drawFiles size files) = files.sumBy
> .checksum` for `Apart` files, building on `fileChecksumCorrect` (`Proofs/Part2.sw:129`)
> and `checksumCorrect` (`Proofs/Part1.sw:173`). Work pointwise with `Disk.at` and the `getOr`
> lemmas, not by unfolding `mapWithIndex`. Tests: `cd aoc && stitchwort test
> Aoc.Year2024.Day09`; `task audit:touched -- Aoc.Year2024.Day09`. Expected: 60 min.

### S4. Day 9: the spec's move on a drawing (Opus, 90 min, ~350 lines)

After S3, and S1 for `findIndex`. It can run beside S2: different files, and a moderate
clash only in imports. **Opus**, because this is the part day 9's note called most of the
work, and the arithmetic (leftmost window, `mapWithIndex` against `drawFiles`) is where the
proof is genuinely hard. Brief:

> Prove group 3 of `docs/proposals/map-set-list-model.md` §4.2 in a new `Proofs/Move.sw`:
> `moveWholeFileGap` and `moveWholeFileNoGap`, with the statements there, plus the pieces:
> `fileStart` on a drawing (`List.findIndexOf`), `count` on a drawing, the leftmost free
> window is the start of the leftmost long-enough gap (`List.findRangeSome`/`None`), and
> the `mapWithIndex` rewrite equals `drawFiles` after `moveTo` (`List.extGetOr`). Reason
> through `Disk.at` throughout. If the statements need another hypothesis, add it and say
> why: S6 must be able to provide it. Day 9's note item 6 (`aoc/NOTES-2024.md:2553`):
> `rewrite` misses unfolded terms, so use `Eq.trans`/`Eq.cong`. Tests: `cd aoc &&
> stitchwort test Aoc.Year2024.Day09`; `task audit:touched -- Aoc.Year2024.Day09`.
> Expected: 90 min.

### S5. Day 9: the starting free space tracks the disk (Sonnet, 75 min, ~200 lines)

After S2 and S3. Brief:

> Prove the first part of group 4 of `docs/proposals/map-set-list-model.md` §4.2: that
> `layoutFrom 0 0 lengths` is `Apart` and draws `blocksFrom 0 lengths` (position by
> position; `layoutBlocks` in `Proofs/Part2.sw` has the flattened form), that
> `joinTouching`'s spans are exactly the gaps of that disk that have a file after them, and
> so that `Tracks (FreeSpace.of (joinTouching layout.snd)) disk bound` holds, with `Tracks`
> as defined there and `bound` the start of the last file of positive length. Mind the
> zero-length files (§4.2, last paragraph): a counterexample means the program is wrong;
> stop and report it. Tests: `cd aoc && stitchwort test Aoc.Year2024.Day09`; `task
> audit:touched -- Aoc.Year2024.Day09`. Expected: 75 min.

### S6. Day 9: the step, the fold, and `part2Correct` (Sonnet, 90 min, ~250 lines; escalate to Opus if stuck)

After S4 and S5. Brief:

> Finish 2024 day 9 part 2 (`docs/proposals/map-set-list-model.md` §4.2, group 4). Prove
> that one `FreeSpace.moveFile` keeps `Tracks` and `Apart`, using S2's `leftmostFitSome`/
> `None` and S4's `moveWholeFileGap`/`NoGap`; that the bound moves to the next file of
> positive length; and that zero-length files change nothing. Then fold it over
> `mapAccumLeft` against the spec's `foldLeft` (write `List.mapAccumLeftInvariant` if
> needed, and move it to std's `List/Lemmas.sw` if it's generic), match the files'
> `fileCount`, and conclude `part2Correct (diskMap: DiskMap): solvePart2 diskMap = part2
> diskMap` with S3's checksum lemma. Rewrite `Proofs/Part2.sw`'s header and the "Not
> proved" paragraph in `aoc/NOTES-2024.md` (around line 2454) to say what's now proved.
> Tests: `cd aoc && stitchwort test Aoc.Year2024.Day09`; `task audit:touched --
> Aoc.Year2024.Day09`; if a std lemma moved, `task audit:touched -- Std.List`, `task
> snap:hashes` and `task test:one -- -E 'binary(hash_stability)'`. If stuck, stop and report
> what you tried, for a rerun on Opus. Expected: 90 min.

Total: about 1,200 lines and 7 hours of lane time. With S1 ∥ S3 and S2 ∥ S4, the
critical path is S3 → S4 → S6, about 4 hours plus merges.

## 6. Risks

1. **The leftmost-window lemma (S4)** is where index arithmetic piles up: windows,
   `freeAt`'s `drop`/`take`/`all`, and "one block earlier would also be free". It is the
   likeliest stage to overrun, which is why it's on Opus and has 90 minutes.
2. **Zero-length files** (§4.2). The straddling gap after `joinTouching`, the program's
   no-op move, and the bound's choice. There may be a real disagreement on some edge disk
   (a disk map starting or ending with a zero-length file, say) that the 14 small-disk tests
   miss. If so the fix is in the program, and S5 or S6 reports it.
3. **The remainder beside the vacated space.** When a file moves into the gap right before
   it, the remainder and the space it leaves form one run on the spec's disk, but the map
   holds only the remainder. The invariant survives because that run starts at or after the
   next bound [inferred from the layout: the next file to move ends before the gap]. S6 has
   to prove that, from the starts of the files still to move decreasing.
4. **`rewrite` against unfolded goals** (`NOTES-2024.md:2553–2567`, day 9's item 6, also
   days 2 and 3). It will recur in S4 and S6; the remedy is `Eq.trans`/`Eq.cong`, as day 9
   did.
5. **Where proofs about `Map` got stuck.** In the friction notes, nowhere on `alter` or
   `adjust` themselves [checked: grep over `aoc/NOTES-*.md` for stuck/missing/out of reach
   near `Map.`/`Set.`]. The stuck points were missing lemmas, now added (2024 day 16's
   `Set.min`/`Map` insert lemmas, `NOTES-2024.md:5001–5023`; day 6's subset size,
   `:2213`), and day 9's invariant. So the std stage is low-risk. The risk sits in S4–S6.
6. **`<=` against `≤`.** `Set.minLeast` concludes with `Ord`'s `<=`. For `Nat` this is `≤`
   by `Nat`'s instance (`core/Ord.sw:75`) [checked], but if elaboration doesn't unfold it,
   S2 needs a one-line bridge.

## 7. Decisions

- **D3070: add a map-of-sets vocabulary to std (`Map.containsIn`, `insertIn`, `removeIn`,
  with `removeIn` dropping empty sets), and port day 9 to it?** [rec: yes. It's the model
  days 6, 9 and 23 already use by hand. It turns day 6's `lineAfterAdd` into a std lemma
  and costs about 60 lines. The names are user-visible std, so they're yours to approve.]
- **D3071: go ahead with the full day 9 part 2 proof, about 1,200 lines in six lanes (7
  hours of lane time)?** [rec: yes. It closes one of the three unproved 2024 parts, and S1's
  `findIndex` and map-of-sets lemmas serve four and three days. If you'd rather spend less,
  stop after S1–S3 (3 hours): they stand on their own.]

**Calls I made** (reversible; say if you disagree):

- The model is key by key (Design B/C), not the sorted list; §2.
- `removeIn` drops empty sets, so equal pairs mean equal maps.
- S1 absorbs SW-1531 (`findIndex` lemmas).
- SW-812 (`Set.card`) isn't needed here. That settles the condition in D2834's
  recommendation ("only if SW-745's list model wants it"): it doesn't.
- S4 runs on Opus as a genuinely hard proof; S6 on Sonnet with escalation.
- `Graph.minLeast` stays as it is; restating it on `Set.minLeast` is optional.
- The proof goes through an in-between picture (`drawFiles`, `Disk.Gap`), not a direct
  map-to-blocks invariant; §4.

## 8. Tickets to file

In order; SW-745 becomes the umbrella and closes with S6.

| Stage | Title | Model | Estimate | Tests | After |
| --- | --- | --- | --- | --- | --- |
| S1 | Std: maps of sets (`containsIn`/`insertIn`/`removeIn`), `Set.minLeast`/`minOfContains`, `minByNone`, `filterEqNone`, `findIndex` lemmas (absorbs SW-1531) | Sonnet | 60 min | `test:lane AREA=std`, `audit:touched -- Std.Set`, `-- Std.List`, `snap:hashes`, `hash_stability` | — |
| S2 | 2024 day 9: `FreeSpace` on `insertIn`/`removeIn`; `leftmostFit` spec | Sonnet | 60 min | day 9 tests, `audit:touched -- Aoc.Year2024.Day09` | S1 |
| S3 | 2024 day 9: `drawFiles`, `Apart`, checksum of a drawing | Sonnet | 60 min | day 9 tests, audit | — |
| S4 | 2024 day 9: the spec's whole-file move on a drawing | Opus | 90 min | day 9 tests, audit | S1, S3 |
| S5 | 2024 day 9: the starting free space tracks the disk (`joinTouching`, layout) | Sonnet | 75 min | day 9 tests, audit | S2, S3 |
| S6 | 2024 day 9: the step, the fold, `part2Correct` | Sonnet (escalate to Opus) | 90 min | day 9 tests, audit; std ones if a lemma moves | S4, S5 |

Findings worth their own small tickets (backlog):

- **2024 day 23's `noneHeld`** (`Day23/Proofs/Part2.sw:74–79`) re-derives
  `Set.missingOfMinNone` (`Set/Spec.sw:138`); a one-line cleanup. DeepSeek, 15 min.
- **2024 day 6 onto `insertIn`** after S1: `Sightlines.add` (`Day06.sw:110–115`) and
  `lineAfterAdd` (`Day06/Proofs/Sightlines.sw:22–33`) replaced by std. DeepSeek, 20 min.
- **2021 day 18's `findUnreducedNone`** (`Day18/Proofs/Parse.sw:23`) onto
  `List.findIndexFromNone`-style std lemmas after S1. DeepSeek, 15 min.
- **Day 9 notes' "Missing std"** (`NOTES-2024.md:2538–2551`): `sumFilterMap` has since been
  added (`List/Lemmas.sw:952`), and `permFlatMapReverse` is used from std
  (`Proofs/Part2.sw:103`). The note still says "None added", so someone should refresh it
  when S6 rewrites the part 2 paragraph (folded into S6's brief).
