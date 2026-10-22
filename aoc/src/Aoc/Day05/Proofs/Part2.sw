-- Day 5, proved: part 2 (merging the ranges and adding up their sizes) is the
-- brute-force count of the ids that some range holds, for every database
-- (`solvePart2Correct`). Kept apart from the program, so `stitchwort run
-- Aoc.Day05.main` doesn't check it.

namespace Aoc.Day05.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Day05 (..)
import Aoc.Day05.Tests (example)
import Std (Bool, Eq, List, Nat, Ordering, Void)

-- Part 2 as the puzzle says it, by brute force: the ids, up to the largest
-- end of a range, that some fresh range holds.
def countFresh (db: Database): Nat :=
  let top := db.fresh.foldLeft (m r => Nat.max m r.to) 0
  List.range (top + 1) |> .count (id => db.fresh.any (r => r.contains id))

test "example brute force" := countFresh (parseDatabase example) == 14

-- Whether some range holds the id.
def covered (rs: List Range) (id: Nat): Bool := rs.any (r => r.contains id)

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
theorem topGe: (z: Nat) -> (rs: List Range) -> z <= rs.foldLeft (m r => Nat.max m r.to) z
  | z, Nil       => Nat.leRefl z
  | z, Cons r rs =>
    calc z
      _ <= Nat.max z r.to                                       := Nat.leMaxLeft z r.to
      _ <= rs.foldLeft (m r => Nat.max m r.to) (Nat.max z r.to) := topGe (Nat.max z r.to) rs

theorem coveredTop: (z: Nat) -> (rs: List Range) -> (id: Nat) -> covered rs id = True -> id <= rs.foldLeft (m r => Nat.max m r.to) z
  | z, Nil,       id, h => Void.exfalso (Bool.falseNotTrue h)
  | z, Cons r rs, id, h =>
    match e: r.contains id with
      | True =>
        calc id
          _ <= r.to                                                  := containsHi r id e
          _ <= Nat.max z r.to                                        := Nat.leMaxRight z r.to
          _ <= rs.foldLeft (m r => Nat.max m r.to) (Nat.max z r.to) := topGe (Nat.max z r.to) rs
      | False => coveredTop (Nat.max z r.to) rs id h

-- Ranges, latest first, each starting after every id the ones after it hold.
def Stacked: List Range -> Prop
  | Nil         => Unit
  | Cons m rest => And (Below m.from rest) (Stacked rest)

-- The first range of a list whose ids are below `n` holds `size` of them.
theorem headCount (m: Range) (rest: List Range) (n: Nat) (b: Below n (Cons m rest)):
    List.occurrences (id => m.contains id) (List.range n) = m.size :=
  match e: Nat.leq m.from m.to with
    | True  => countBelow m n (b m.to (coveredFirst m rest m.to (Nat.betweenYes m.from m.to m.to e (Nat.leRefl m.to))))
    | False => countEmpty m e (List.range n)

-- Stacked ranges hold different ids, so the ids below `n` they hold number
-- the sum of their sizes.
theorem stackedCount (n: Nat): (ms: List Range) -> Stacked ms -> Below n ms ->
    List.occurrences (id => covered ms id) (List.range n) = ms.sumBy Range.size
  | Nil,         s,             b => List.occurrencesNone (id => covered Nil id) (id => rfl) (List.range n)
  | Cons m rest, Both bm srest, b =>
    calc List.occurrences (id => covered (Cons m rest) id) (List.range n)
      _ = List.occurrences (id => m.contains id) (List.range n) + List.occurrences (id => covered rest id) (List.range n)
          := List.occurrencesOr (id => m.contains id) (id => covered rest id)
               (id h =>
                 match t: covered rest id with
                   | True  => Void.exfalso (Nat.lessIrrefl id (Nat.leTrans (Succ id) m.from id (bm id t) (containsLo m id h)))
                   | False => rfl)
               (List.range n)
      _ = m.size + List.occurrences (id => covered rest id) (List.range n) := rewrite headCount m rest n b
      _ = m.size + rest.sumBy Range.size
          := rewrite stackedCount n rest srest (id h => b id (coveredRest m rest id h))
      _ = (Cons m rest).sumBy Range.size := Eq.sym (List.sumByCons Range.size m rest)

-- Merging keeps the covered ids (`stackCovers`), and the merged ranges,
-- latest first, are stacked (`stackStacked`): each starts after every id
-- the earlier ones hold. So no id is counted twice, and the sizes add up to
-- the count (`stackedCount`).
theorem solvePart2Correct (db: Database): solvePart2 db = countFresh db :=
  let top := db.fresh.foldLeft (m r => Nat.max m r.to) 0
  calc solvePart2 db
    _ = (stack db.fresh).sumBy Range.size := List.sumByReverse Range.size (stack db.fresh)
    _ = List.occurrences (id => covered (stack db.fresh) id) (List.range (top + 1))
        := Eq.sym (stackedCount (top + 1) (stack db.fresh) (stackStacked db.fresh)
             (id h => Nat.ltCongRight id (Succ top) (top + 1) (Eq.sym (Nat.addOne top))
               (Nat.leLessSucc id top (coveredTop 0 db.fresh id (Eq.trans (Eq.sym (stackCovers db.fresh id)) h)))))
    _ = List.occurrences (id => covered db.fresh id) (List.range (top + 1))
        := List.occurrencesCongr (id => covered (stack db.fresh) id) (id => covered db.fresh id) (stackCovers db.fresh) (List.range (top + 1))
    _ = countFresh db := Eq.sym (List.countOccurrences (id => covered db.fresh id) (List.range (top + 1)))

-- The merged ranges, latest first: `merge` before its `reverse`.
def stack (ranges: List Range): List Range :=
  ranges
    |> .sortBy (a b => Nat.compare a.from b.from)
    |> .foldLeft absorb []

theorem stackSorted (ranges: List Range):
    List.Sorted (x y => Ordering.isLessEq (Nat.compare x.from y.from)) (ranges.sortBy (a b => Nat.compare a.from b.from)) :=
  List.sortBySorted (a b => Nat.compare (Range.from a) (Range.from b)) (x y h => Nat.compareTotal x.from y.from h) ranges

theorem stackCovers (ranges: List Range) (id: Nat): covered (stack ranges) id = covered ranges id :=
  Eq.trans (foldCovers id Nil (ranges.sortBy (a b => Nat.compare a.from b.from)) (stackSorted ranges) (fitsNil (ranges.sortBy (a b => Nat.compare a.from b.from))))
    (List.anyPerm (r => Range.contains r id) (ranges.sortBy (a b => Nat.compare a.from b.from)) ranges (List.sortByPerm (a b => Nat.compare (Range.from a) (Range.from b)) ranges))

theorem stackStacked (ranges: List Range): Stacked (stack ranges) :=
  foldStacked Nil (ranges.sortBy (a b => Nat.compare a.from b.from)) (stackSorted ranges) (fitsNil (ranges.sortBy (a b => Nat.compare a.from b.from))) Trivial

-- Merging keeps exactly the covered ids.
theorem mergeCovers (ranges: List Range) (id: Nat): (merge ranges).any (r => r.contains id) = ranges.any (r => r.contains id) :=
  Eq.trans (List.anyPerm (r => Range.contains r id) (merge ranges) (stack ranges) (List.reversePerm (stack ranges))) (stackCovers ranges id)

-- The latest merged range starts no later than `b`.
def LoAtMost (b: Nat): List Range -> Prop
  | Nil         => Unit
  | Cons last _ => last.from <= b

-- Two ranges, the second starting inside the first or just after it, hold
-- the ids of their merge.
theorem mergedContains (a: Range) (r: Range) (id: Nat) (h1: a.from <= r.from) (h2: r.from <= a.to + 1):
    Range.contains { from = a.from, to = Nat.max a.to r.to } id = (a.contains id || r.contains id) :=
  match t: Nat.leq a.from id, i: Nat.leq id a.to with
    | True, True =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.to r.to))) (Nat.leTrans id a.to (Nat.max a.to r.to) i (Nat.leMaxLeft a.to r.to))
    | True, False =>
      Eq.trans (Bool.decTrueToBool (Nat.leq id (Nat.max a.to r.to)))
        (Eq.trans (Nat.leqMaxAbove id a.to r.to i)
          (Eq.sym (Nat.betweenFrom r.from r.to id
            (Nat.leTrans r.from (a.to + 1) id h2 (Nat.leCongLeft (Succ a.to) (a.to + 1) id (Eq.sym (Nat.addOne a.to)) (Nat.leqFalse id a.to i))))))
    | False, _ => Eq.sym (Nat.betweenBelow r.from r.to id (Nat.leqFalseOfLess id r.from (Nat.leTrans (Succ id) a.from r.from (Nat.leqFalse a.from id t) h1)))

theorem absorbCovers (r: Range) (id: Nat): (merged: List Range) -> LoAtMost r.from merged ->
    covered (absorb merged r) id = (covered merged id || r.contains id)
  | Nil,               ok => Bool.orFalse (r.contains id)
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True =>
        calc (Range.contains { from = last.from, to = Nat.max last.to r.to } id || covered earlier id)
          _ = ((last.contains id || r.contains id) || covered earlier id)  := rewrite mergedContains last r id ok e
          _ = (last.contains id || (r.contains id || covered earlier id))  := Bool.orAssoc (last.contains id) (r.contains id) (covered earlier id)
          _ = (last.contains id || (covered earlier id || r.contains id))  := rewrite Bool.orComm (r.contains id) (covered earlier id)
          _ = ((last.contains id || covered earlier id) || r.contains id)  := Eq.sym (Bool.orAssoc (last.contains id) (covered earlier id) (r.contains id))
      | False => Bool.orComm (r.contains id) (covered (Cons last earlier) id)

theorem absorbLo (r: Range) (b: Nat) (h: r.from <= b): (merged: List Range) -> LoAtMost r.from merged -> LoAtMost b (absorb merged r)
  | Nil,               ok => h
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True =>
        calc last.from
          _ <= r.from := ok
          _ <= b    := h
      | False => h

theorem absorbStacked (r: Range): (merged: List Range) -> LoAtMost r.from merged -> Stacked merged -> Stacked (absorb merged r)
  | Nil,               ok, s           => Both (id h => Void.exfalso (Bool.falseNotTrue h)) Trivial
  | Cons last earlier, ok, Both b rest =>
    match e: Nat.leq r.from (last.to + 1) with
      | True  => Both b rest
      | False =>
        Both
          (id h =>
            match i: last.contains id with
              | True =>
                calc id
                  _ < Succ last.to := containsHi last id i
                  _ = last.to + 1  := Eq.sym (Nat.addOne last.to)
                  _ <= r.from        := Nat.lessLe (last.to + 1) r.from (Nat.leqFalse r.from (last.to + 1) e)
              | False =>
                calc Succ id
                  _ <= last.from := b id h
                  _ <= r.from    := ok)
          (Both b rest)

-- Folding: the next range starts no earlier than the latest merged one.
def Fits (merged: List Range): List Range -> Prop
  | Nil      => Unit
  | Cons x _ => LoAtMost x.from merged

theorem fitsNil: (xs: List Range) -> Fits Nil xs
  | Nil       => Trivial
  | Cons x xs => Trivial

theorem fitsStep (acc: List Range) (x: Range): (xs: List Range) -> LoAtMost x.from acc ->
    List.LeHead (a b => Ordering.isLessEq (Nat.compare a.from b.from)) x xs -> Fits (absorb acc x) xs
  | Nil,       ok, hx => Trivial
  | Cons y ys, ok, hx => absorbLo x y.from (Eq.trans (Eq.sym (Nat.compareLeq x.from y.from)) hx) acc ok

theorem foldCovers (id: Nat): (acc: List Range) -> (xs: List Range) ->
    List.Sorted (a b => Ordering.isLessEq (Nat.compare a.from b.from)) xs -> Fits acc xs ->
    covered (xs.foldLeft absorb acc) id = (covered acc id || covered xs id)
  | acc, Nil,       s,           ok => Eq.sym (Bool.orFalse (covered acc id))
  | acc, Cons x xs, Both hx sxs, ok =>
    calc covered (xs.foldLeft absorb (absorb acc x)) id
      _ = (covered (absorb acc x) id || covered xs id)         := foldCovers id (absorb acc x) xs sxs (fitsStep acc x xs ok hx)
      _ = ((covered acc id || x.contains id) || covered xs id) := rewrite absorbCovers x id acc ok
      _ = (covered acc id || covered (Cons x xs) id)           := Bool.orAssoc (covered acc id) (x.contains id) (covered xs id)

theorem foldStacked: (acc: List Range) -> (xs: List Range) ->
    List.Sorted (a b => Ordering.isLessEq (Nat.compare a.from b.from)) xs -> Fits acc xs -> Stacked acc -> Stacked (xs.foldLeft absorb acc)
  | acc, Nil,       s,           ok, st => st
  | acc, Cons x xs, Both hx sxs, ok, st => foldStacked (absorb acc x) xs sxs (fitsStep acc x xs ok hx) (absorbStacked x acc ok st)
