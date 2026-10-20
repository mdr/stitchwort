-- Advent of Code 2025, day 5: a list of fresh ingredient id ranges (a-b,
-- both ends included), a blank line, then a list of ingredient ids. Part 1
-- counts the ids inside some range. Part 2 counts the numbers covered by
-- the ranges together, whether or not they appear in the list of ids.
--
--   $ cd aoc && stitchwort run Aoc.Day05.main < inputs/day05.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Part 1 checks every id against every range. Part 2 can't list the numbers
-- (there are about 4 * 10^14), so it merges the ranges instead: sorted by
-- start, a range either overlaps or touches the previous merged range (and
-- extends it) or starts a new one. The merged ranges are disjoint, so their
-- sizes add up. `solvePart2Correct` proves that, for every database: part 2
-- is the brute-force count of the ids some range holds.

namespace Aoc.Day05
import Aoc.Common (Range)

def main(): {IO} () :=
  let database := parseDatabase (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 database}"
  IO.print "Part 2: ${solvePart2 database}"

-- The fresh ranges, and the available ids.
type Database = { fresh: List Range, available: List Nat }

-- A line is a range if it reads as one, an id if it reads as a number, and
-- is skipped otherwise (the blank line).
def parseDatabase (lines: List Text): Database :=
  { fresh = lines.mapMaybe Range.parse, available = lines.mapMaybe Text.toNat }

def example: List Text :=
  [ "3-5", "10-14", "16-20", "12-18", "", "1", "5", "8", "11", "17", "32" ]

test "example parse" := (parseDatabase example).available == [1, 5, 8, 11, 17, 32]

-- Part 1: the available ids that are fresh.
def solvePart1 (db: Database): Nat :=
  db.available.count (\id => db.fresh.any (\r => r.contains id))

test "example part 1" := solvePart1 (parseDatabase example) == 3

-- Part 2: every id the fresh ranges cover.
def solvePart2 (db: Database): Nat := merge db.fresh |> .sumBy Range.size

test "example part 2" := solvePart2 (parseDatabase example) == 14
test "no ranges" := solvePart2 { fresh = [], available = [] } == 0

-- Part 2 as the puzzle says it, by brute force: the ids, up to the largest
-- end of a range, that some fresh range holds.
def countFresh (db: Database): Nat :=
  let top := db.fresh.foldLeft (\m r => Nat.max m r.hi) 0
  List.range (top + 1) |> .count (\id => db.fresh.any (\r => r.contains id))

test "example brute force" := countFresh (parseDatabase example) == 14

-- Whether some range holds the id.
def covered (rs: List Range) (id: Nat): Bool := rs.any (\r => r.contains id)

theorem coveredFirst (m: Range) (rest: List Range) (id: Nat) (h: m.contains id = True): covered (Cons m rest) id = True :=
  rewrite h

theorem coveredRest (m: Range) (rest: List Range) (id: Nat) (h: covered rest id = True): covered (Cons m rest) id = True :=
  rewrite h in Bool.orTrue (m.contains id)

theorem coveredSkip (m: Range) (rest: List Range) (id: Nat) (f: m.contains id = False) (h: covered (Cons m rest) id = True): covered rest id = True :=
  calc covered rest id
    _ = (m.contains id || covered rest id) := rewrite f
    _ = True                               := h

-- Every id the ranges hold is below `b`.
def Below (b: Nat) (rs: List Range): Prop := (id: Nat) -> covered rs id = True -> id < b

-- Every id the ranges hold is at most the largest end.
theorem topGe: (z: Nat) -> (rs: List Range) -> z <= rs.foldLeft (\m r => Nat.max m r.hi) z
  | z, Nil       => Nat.leRefl z
  | z, Cons r rs =>
    calc z
      _ <= Nat.max z r.hi                                       := Nat.leMaxLeft z r.hi
      _ <= rs.foldLeft (\m r => Nat.max m r.hi) (Nat.max z r.hi) := topGe (Nat.max z r.hi) rs

theorem coveredTop: (z: Nat) -> (rs: List Range) -> (id: Nat) -> covered rs id = True -> id <= rs.foldLeft (\m r => Nat.max m r.hi) z
  | z, Nil,       id, h => Void.exfalso (Bool.falseNotTrue h)
  | z, Cons r rs, id, h =>
    match e: r.contains id with
      | True =>
        calc id
          _ <= r.hi                                                  := Range.containsHi r id e
          _ <= Nat.max z r.hi                                        := Nat.leMaxRight z r.hi
          _ <= rs.foldLeft (\m r => Nat.max m r.hi) (Nat.max z r.hi) := topGe (Nat.max z r.hi) rs
      | False => coveredTop (Nat.max z r.hi) rs id h

-- Ranges, latest first, each starting after every id the ones after it hold.
def Stacked: List Range -> Prop
  | Nil         => Unit
  | Cons m rest => And (Below m.lo rest) (Stacked rest)

-- The first range of a list whose ids are below `n` holds `size` of them.
theorem headCount (m: Range) (rest: List Range) (n: Nat) (b: Below n (Cons m rest)):
    List.occurrences (\id => m.contains id) (List.range n) = m.size :=
  match e: Nat.leq m.lo m.hi with
    | True  => Range.countBelow m n (b m.hi (coveredFirst m rest m.hi (Nat.betweenYes m.lo m.hi m.hi e (Nat.leRefl m.hi))))
    | False => Range.countEmpty m e (List.range n)

-- Stacked ranges hold different ids, so the ids below `n` they hold number
-- the sum of their sizes.
theorem stackedCount (n: Nat): (ms: List Range) -> Stacked ms -> Below n ms ->
    List.occurrences (\id => covered ms id) (List.range n) = ms.sumBy Range.size
  | Nil,         s,             b => List.occurrencesNone (\id => covered Nil id) (\id => rfl) (List.range n)
  | Cons m rest, Both bm srest, b =>
    calc List.occurrences (\id => covered (Cons m rest) id) (List.range n)
      _ = List.occurrences (\id => m.contains id) (List.range n) + List.occurrences (\id => covered rest id) (List.range n)
          := List.occurrencesOr (\id => m.contains id) (\id => covered rest id)
               (\id h =>
                 match t: covered rest id with
                   | True  => Void.exfalso (Nat.lessIrrefl id (Nat.leTrans (Succ id) m.lo id (bm id t) (Range.containsLo m id h)))
                   | False => rfl)
               (List.range n)
      _ = m.size + List.occurrences (\id => covered rest id) (List.range n) := rewrite headCount m rest n b
      _ = m.size + rest.sumBy Range.size
          := rewrite stackedCount n rest srest (\id h => b id (coveredRest m rest id h))
      _ = (Cons m rest).sumBy Range.size := Eq.sym (List.sumByCons Range.size m rest)


-- Merging keeps the covered ids (`stackCovers`), and the merged ranges,
-- latest first, are stacked (`stackStacked`): each starts after every id
-- the earlier ones hold. So no id is counted twice, and the sizes add up to
-- the count (`stackedCount`).
theorem solvePart2Correct (db: Database): solvePart2 db = countFresh db :=
  let top := db.fresh.foldLeft (\m r => Nat.max m r.hi) 0
  calc solvePart2 db
    _ = (stack db.fresh).sumBy Range.size := List.sumByReverse Range.size (stack db.fresh)
    _ = List.occurrences (\id => covered (stack db.fresh) id) (List.range (top + 1))
        := Eq.sym (stackedCount (top + 1) (stack db.fresh) (stackStacked db.fresh)
             (\id h => Nat.ltCongRight id (Succ top) (top + 1) (Eq.sym (Nat.addOne top))
               (Nat.leLessSucc id top (coveredTop 0 db.fresh id (Eq.trans (Eq.sym (stackCovers db.fresh id)) h)))))
    _ = List.occurrences (\id => covered db.fresh id) (List.range (top + 1))
        := List.occurrencesCongr (\id => covered (stack db.fresh) id) (\id => covered db.fresh id) (stackCovers db.fresh) (List.range (top + 1))
    _ = countFresh db := Eq.sym (List.countOccurrences (\id => covered db.fresh id) (List.range (top + 1)))

-- Merge ranges that overlap or touch. The list is sorted by start, then
-- folded into a list of merged ranges with the latest first.
def merge (ranges: List Range): List Range :=
  ranges
    |> .sortBy (\a b => Nat.compare a.lo b.lo)
    |> .foldLeft absorb []
    |> .reverse

test "example merged" := merge (parseDatabase example).fresh == [{ lo = 3, hi = 5 }, { lo = 10, hi = 20 }]
test "touching ranges merge" := merge [{ lo = 4, hi = 6 }, { lo = 1, hi = 3 }] == [{ lo = 1, hi = 6 }]
test "nested range" := merge [{ lo = 1, hi = 9 }, { lo = 2, hi = 3 }] == [{ lo = 1, hi = 9 }]
test "gap stays" := merge [{ lo = 1, hi = 2 }, { lo = 4, hi = 5 }] == [{ lo = 1, hi = 2 }, { lo = 4, hi = 5 }]

-- The merged ranges, latest first: `merge` before its `reverse`.
def stack (ranges: List Range): List Range :=
  ranges
    |> .sortBy (\a b => Nat.compare a.lo b.lo)
    |> .foldLeft absorb []

theorem stackSorted (ranges: List Range):
    List.Sorted (\x y => Ordering.isLessEq (Nat.compare x.lo y.lo)) (ranges.sortBy (\a b => Nat.compare a.lo b.lo)) :=
  List.sortBySorted (\a b => Nat.compare (Range.lo a) (Range.lo b)) (\x y h => Nat.compareTotal x.lo y.lo h) ranges

theorem stackCovers (ranges: List Range) (id: Nat): covered (stack ranges) id = covered ranges id :=
  Eq.trans (foldCovers id Nil (ranges.sortBy (\a b => Nat.compare a.lo b.lo)) (stackSorted ranges) (fitsNil (ranges.sortBy (\a b => Nat.compare a.lo b.lo))))
    (List.anyPerm (\r => Range.contains r id) (ranges.sortBy (\a b => Nat.compare a.lo b.lo)) ranges (List.sortByPerm (\a b => Nat.compare (Range.lo a) (Range.lo b)) ranges))

theorem stackStacked (ranges: List Range): Stacked (stack ranges) :=
  foldStacked Nil (ranges.sortBy (\a b => Nat.compare a.lo b.lo)) (stackSorted ranges) (fitsNil (ranges.sortBy (\a b => Nat.compare a.lo b.lo))) Trivial

-- Merging keeps exactly the covered ids.
theorem mergeCovers (ranges: List Range) (id: Nat): (merge ranges).any (\r => r.contains id) = ranges.any (\r => r.contains id) :=
  Eq.trans (List.anyPerm (\r => Range.contains r id) (merge ranges) (stack ranges) (List.reversePerm (stack ranges))) (stackCovers ranges id)

-- Add a range, starting no earlier than the ones already merged, to them.
def absorb (merged: List Range) (r: Range): List Range :=
  match merged with
    | Nil => [r]
    | Cons last earlier =>
      if r.lo <= last.hi + 1
      then Cons { lo = last.lo, hi = Nat.max last.hi r.hi } earlier
      else Cons r merged

-- The latest merged range starts no later than `b`.
def LoAtMost (b: Nat): List Range -> Prop
  | Nil         => Unit
  | Cons last _ => last.lo <= b

-- Two ranges, the second starting inside the first or just after it, hold
-- the ids of their merge.
theorem mergedContains (a: Range) (r: Range) (id: Nat) (h1: a.lo <= r.lo) (h2: r.lo <= a.hi + 1):
    Range.contains { lo = a.lo, hi = Nat.max a.hi r.hi } id = (a.contains id || r.contains id) :=
  match t: Nat.leq a.lo id, i: Nat.leq id a.hi with
    | True, True =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.hi r.hi))) (Nat.leTrans id a.hi (Nat.max a.hi r.hi) i (Nat.leMaxLeft a.hi r.hi))
    | True, False =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.hi r.hi)))
        (Eq.trans (Nat.leqMaxAbove id a.hi r.hi i)
          (Eq.sym (Nat.betweenFrom r.lo r.hi id
            (Nat.leTrans r.lo (a.hi + 1) id h2 (Nat.leCongLeft (Succ a.hi) (a.hi + 1) id (Eq.sym (Nat.addOne a.hi)) (Nat.leqFalse id a.hi i))))))
    | False, _ => Eq.sym (Nat.betweenBelow r.lo r.hi id (Nat.leqFalseOfLess id r.lo (Nat.leTrans (Succ id) a.lo r.lo (Nat.leqFalse a.lo id t) h1)))

theorem absorbCovers (r: Range) (id: Nat): (merged: List Range) -> LoAtMost r.lo merged ->
    covered (absorb merged r) id = (covered merged id || r.contains id)
  | Nil,               ok => Bool.orFalse (r.contains id)
  | Cons last earlier, ok =>
    match e: Nat.leq r.lo (last.hi + 1) with
      | True =>
        calc (Range.contains { lo = last.lo, hi = Nat.max last.hi r.hi } id || covered earlier id)
          _ = ((last.contains id || r.contains id) || covered earlier id)  := rewrite mergedContains last r id ok e
          _ = (last.contains id || (r.contains id || covered earlier id))  := Bool.orAssoc (last.contains id) (r.contains id) (covered earlier id)
          _ = (last.contains id || (covered earlier id || r.contains id))  := rewrite Bool.orComm (r.contains id) (covered earlier id)
          _ = ((last.contains id || covered earlier id) || r.contains id)  := Eq.sym (Bool.orAssoc (last.contains id) (covered earlier id) (r.contains id))
      | False => Bool.orComm (r.contains id) (covered (Cons last earlier) id)

theorem absorbLo (r: Range) (b: Nat) (h: r.lo <= b): (merged: List Range) -> LoAtMost r.lo merged -> LoAtMost b (absorb merged r)
  | Nil,               ok => h
  | Cons last earlier, ok =>
    match e: Nat.leq r.lo (last.hi + 1) with
      | True =>
        calc last.lo
          _ <= r.lo := ok
          _ <= b    := h
      | False => h

theorem absorbStacked (r: Range): (merged: List Range) -> LoAtMost r.lo merged -> Stacked merged -> Stacked (absorb merged r)
  | Nil,               ok, s           => Both (\id h => Void.exfalso (Bool.falseNotTrue h)) Trivial
  | Cons last earlier, ok, Both b rest =>
    match e: Nat.leq r.lo (last.hi + 1) with
      | True  => Both b rest
      | False =>
        Both
          (\id h =>
            match i: last.contains id with
              | True =>
                calc id
                  _ < Succ last.hi := Range.containsHi last id i
                  _ = last.hi + 1  := Eq.sym (Nat.addOne last.hi)
                  _ <= r.lo        := Nat.lessLe (last.hi + 1) r.lo (Nat.leqFalse r.lo (last.hi + 1) e)
              | False =>
                calc Succ id
                  _ <= last.lo := b id h
                  _ <= r.lo    := ok)
          (Both b rest)

-- Folding: the next range starts no earlier than the latest merged one.
def Fits (merged: List Range): List Range -> Prop
  | Nil      => Unit
  | Cons x _ => LoAtMost x.lo merged

theorem fitsNil: (xs: List Range) -> Fits Nil xs
  | Nil       => Trivial
  | Cons x xs => Trivial

theorem fitsStep (acc: List Range) (x: Range): (xs: List Range) -> LoAtMost x.lo acc ->
    List.LeHead (\a b => Ordering.isLessEq (Nat.compare a.lo b.lo)) x xs -> Fits (absorb acc x) xs
  | Nil,       ok, hx => Trivial
  | Cons y ys, ok, hx => absorbLo x y.lo (Eq.trans (Eq.sym (Nat.compareLeq x.lo y.lo)) hx) acc ok

theorem foldCovers (id: Nat): (acc: List Range) -> (xs: List Range) ->
    List.Sorted (\a b => Ordering.isLessEq (Nat.compare a.lo b.lo)) xs -> Fits acc xs ->
    covered (xs.foldLeft absorb acc) id = (covered acc id || covered xs id)
  | acc, Nil,       s,           ok => Eq.sym (Bool.orFalse (covered acc id))
  | acc, Cons x xs, Both hx sxs, ok =>
    calc covered (xs.foldLeft absorb (absorb acc x)) id
      _ = (covered (absorb acc x) id || covered xs id)         := foldCovers id (absorb acc x) xs sxs (fitsStep acc x xs ok hx)
      _ = ((covered acc id || x.contains id) || covered xs id) := rewrite absorbCovers x id acc ok
      _ = (covered acc id || covered (Cons x xs) id)           := Bool.orAssoc (covered acc id) (x.contains id) (covered xs id)

theorem foldStacked: (acc: List Range) -> (xs: List Range) ->
    List.Sorted (\a b => Ordering.isLessEq (Nat.compare a.lo b.lo)) xs -> Fits acc xs -> Stacked acc -> Stacked (xs.foldLeft absorb acc)
  | acc, Nil,       s,           ok, st => st
  | acc, Cons x xs, Both hx sxs, ok, st => foldStacked (absorb acc x) xs sxs (fitsStep acc x xs ok hx) (absorbStacked x acc ok st)
