-- Day 5, proved: part 2 (merging the ranges and adding up their sizes) is the
-- brute-force count of the ids that some range holds, for every database
-- (`solvePart2Correct`). Kept apart from the program, so `stitchwort run
-- Aoc.Year2025.Day05.main` doesn't check it.

namespace Aoc.Year2025.Day05.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Year2025.Day05 (..)
import Aoc.Year2025.Day05.Spec (..)
import Std (Bool, Eq, Fail, List, Nat, Ordering, Void)

-- Whether some range holds the id.
def covered (rs: List Range) (id: Nat): Bool := rs.any (r => r.contains id)

theorem coveredFirst (m: Range) (rest: List Range) (id: Nat) (h: m.contains id = True): covered (Cons m rest) id = True :=
  rewrite h

theorem coveredRest (m: Range) (rest: List Range) (id: Nat) (h: covered rest id = True): covered (Cons m rest) id = True :=
  rewrite h in Bool.orTrue (m.contains id)

theorem coveredSkip (m: Range) (rest: List Range) (id: Nat) (f: m.contains id = False) (h: covered (Cons m rest) id = True): covered rest id = True :=
  calc covered rest id
    _ = (m.contains id ∨ covered rest id) := rewrite f
    _ = True := h

-- Every id the ranges hold is below `b`.
def Below (b: Nat) (rs: List Range): Prop := (id: Nat) → covered rs id = True → id < b

-- Every id the ranges hold is at most the largest end.
theorem topGe: (z: Nat) → (rs: List Range) → z ≤ rs.foldLeft z (m r => Nat.max m r.to)
  | z, Nil => omega
  | z, Cons r rs => omega [topGe (Nat.max z r.to) rs]

theorem coveredTop: (z: Nat) → (rs: List Range) → (id: Nat) → covered rs id = True → id ≤ rs.foldLeft z (m r => Nat.max m r.to)
  | z, Nil, id, h => Void.exfalso (Bool.falseNotTrue h)
  | z, Cons r rs, id, h =>
    match e: r.contains id with
      | True => omega [topGe (Nat.max z r.to) rs]
      | False => coveredTop (Nat.max z r.to) rs id h

-- Ranges, latest first, each starting after every id the ones after it hold.
def Stacked: List Range → Prop
  | Nil => Unit
  | Cons m rest => Below m.from rest ∧ Stacked rest

-- The first range of a list whose ids are below `n` holds `size` of them.
theorem headCount (m: Range) (rest: List Range) (n: Nat) (b: Below n (Cons m rest)):
    List.occurrences (List.range n) (id => m.contains id) = m.size :=
  match e: Nat.leq m.from m.to with
    | True => countBelow m n (b m.to (coveredFirst m rest m.to (Nat.betweenYes m.from m.to m.to e omega)))
    | False => countEmpty m e (List.range n)

-- Stacked ranges hold different ids, so the ids below `n` they hold number
-- the sum of their sizes.
theorem stackedCount (n: Nat): (ms: List Range) → Stacked ms → Below n ms →
    List.occurrences (List.range n) (id => covered ms id) = ms.sumBy Range.size
  | Nil, s, b => List.occurrencesNone (List.range n) (id => covered Nil id) (id => rfl)
  | Cons m rest, Both bm srest, b =>
    calc List.occurrences (List.range n) (id => covered (Cons m rest) id)
      _ = List.occurrences (List.range n) (id => m.contains id) + List.occurrences (List.range n) (id => covered rest id)
        := List.occurrencesOr (List.range n) (id => m.contains id)
          (id => covered rest id)
          (id h =>
            match t: covered rest id with
              | True => omega [bm id t, containsLo m id h]
              | False => rfl)
      _ = m.size + List.occurrences (List.range n) (id => covered rest id) := rewrite headCount m rest n b
      _ = m.size + rest.sumBy Range.size
        := rewrite stackedCount n rest srest (id h => b id (coveredRest m rest id h))
      _ = (Cons m rest).sumBy Range.size := Eq.sym (List.sumByCons rest m Range.size)

-- Merging keeps the covered ids (`stackCovers`), and the merged ranges,
-- latest first, are stacked (`stackStacked`): each starts after every id
-- the earlier ones hold. So no id is counted twice, and the sizes add up to
-- the count (`stackedCount`).
theorem solvePart2Correct (db: Database): solvePart2 db = countFresh db :=
  let top := db.fresh.foldLeft 0 (m r => Nat.max m r.to)
  calc solvePart2 db
    _ = (stack db.fresh).sumBy Range.size := List.sumByReverse (stack db.fresh) Range.size
    _ = List.occurrences (List.range (top + 1)) (id => covered (stack db.fresh) id)
      := Eq.sym (stackedCount (top + 1) (stack db.fresh) (stackStacked db.fresh)
        (id h => omega [coveredTop 0 db.fresh id (Eq.trans (Eq.sym (stackCovers db.fresh id)) h)]))
    _ = List.occurrences (List.range (top + 1)) (id => covered db.fresh id)
      := rewrite stackCovers db.fresh _
    _ = countFresh db := Eq.sym (List.countOccurrences (List.range (top + 1)) (id => covered db.fresh id))

-- The merged ranges, latest first: `merge` before its `reverse`.
def stack (ranges: List Range): List Range :=
  ranges
    |> .sort
    |> .foldLeft [] absorb

theorem stackSorted (ranges: List Range):
    List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) ranges.sort :=
  List.sortSorted ranges

theorem stackCovers (ranges: List Range) (id: Nat): covered (stack ranges) id = covered ranges id :=
  Eq.trans (foldCovers id Nil ranges.sort (stackSorted ranges) (fitsNil ranges.sort))
    (List.anyPerm ranges.sort ranges (List.sortPerm ranges) (r => Range.contains r id))

theorem stackStacked (ranges: List Range): Stacked (stack ranges) :=
  foldStacked Nil ranges.sort (stackSorted ranges) (fitsNil ranges.sort) Trivial

-- Merging keeps exactly the covered ids.
theorem mergeCovers (ranges: List Range) (id: Nat): (merge ranges).any (r => r.contains id) = ranges.any (r => r.contains id) :=
  Eq.trans (List.anyPerm (merge ranges) (stack ranges) (List.reversePerm (stack ranges)) (r => Range.contains r id)) (stackCovers ranges id)

-- The latest merged range starts no later than `b`.
def LoAtMost (b: Nat): List Range → Prop
  | Nil => Unit
  | Cons last _ => last.from ≤ b

-- Two ranges, the second starting inside the first or just after it, hold
-- the ids of their merge.
theorem mergedContains (a: Range) (r: Range) (id: Nat) (h1: a.from ≤ r.from) (h2: r.from ≤ a.to + 1):
    Range.contains { from = a.from, to = Nat.max a.to r.to } id = (a.contains id ∨ r.contains id) :=
  match t: Nat.leq a.from id, i: Nat.leq id a.to with
    | True, True =>
      omega
    | True, False =>
      Eq.trans (Nat.leqMaxAbove id a.to r.to i)
        (Eq.sym (Nat.betweenFrom r.from r.to id omega))
    | False, _ => Eq.sym (Nat.betweenBelow r.from r.to id omega)

theorem absorbCovers (r: Range) (id: Nat): (merged: List Range) → LoAtMost r.from merged →
    covered (absorb merged r) id = (covered merged id ∨ r.contains id)
  | Nil, ok => Bool.orFalse (r.contains id)
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True =>
        calc (Range.contains { from = last.from, to = Nat.max last.to r.to } id ∨ covered earlier id)
          _ = ((last.contains id ∨ r.contains id) ∨ covered earlier id) := rewrite mergedContains last r id ok e
          _ = (last.contains id ∨ (r.contains id ∨ covered earlier id)) := Bool.orAssoc (last.contains id) (r.contains id) (covered earlier id)
          _ = (last.contains id ∨ (covered earlier id ∨ r.contains id)) := rewrite Bool.orComm (r.contains id) (covered earlier id)
          _ = ((last.contains id ∨ covered earlier id) ∨ r.contains id) := Eq.sym (Bool.orAssoc (last.contains id) (covered earlier id) (r.contains id))
      | False => Bool.orComm (r.contains id) (covered (Cons last earlier) id)

theorem absorbLo (r: Range) (b: Nat) (h: r.from ≤ b): (merged: List Range) → LoAtMost r.from merged → LoAtMost b (absorb merged r)
  | Nil, ok => h
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True => omega
      | False => h

theorem absorbStacked (r: Range): (merged: List Range) → LoAtMost r.from merged → Stacked merged → Stacked (absorb merged r)
  | Nil, ok, s => Both (id h => Void.exfalso (Bool.falseNotTrue h)) Trivial
  | Cons last earlier, ok, Both b rest =>
    match e: Nat.leq r.from (last.to + 1) with
      | True => Both b rest
      | False =>
        Both
          (id h =>
            match i: last.contains id with
              | True => omega
              | False => omega [b id h])
          (Both b rest)

-- Folding: the next range starts no earlier than the latest merged one.
def Fits (merged: List Range): List Range → Prop
  | Nil => Unit
  | Cons x _ => LoAtMost x.from merged

theorem fitsNil: (xs: List Range) → Fits Nil xs
  | Nil => Trivial
  | Cons x xs => Trivial

theorem fitsStep (acc: List Range) (x: Range): (xs: List Range) → LoAtMost x.from acc →
    List.LeHead (a b => Ordering.isLessEq (Ord.compare a b)) x xs → Fits (absorb acc x) xs
  | Nil, ok, hx => Trivial
  | Cons y ys, ok, hx => absorbLo x y.from (compareFrom x y hx) acc ok

theorem foldCovers (id: Nat): (acc: List Range) → (xs: List Range) →
    List.Sorted (a b => Ordering.isLessEq (Ord.compare a b)) xs → Fits acc xs →
    covered (xs.foldLeft acc absorb) id = (covered acc id ∨ covered xs id)
  | acc, Nil, s, ok => Eq.sym (Bool.orFalse (covered acc id))
  | acc, Cons x xs, Both hx sxs, ok =>
    calc covered (xs.foldLeft (absorb acc x) absorb) id
      _ = (covered (absorb acc x) id ∨ covered xs id) := foldCovers id (absorb acc x) xs sxs (fitsStep acc x xs ok hx)
      _ = ((covered acc id ∨ x.contains id) ∨ covered xs id) := rewrite absorbCovers x id acc ok
      _ = (covered acc id ∨ covered (Cons x xs) id) := Bool.orAssoc (covered acc id) (x.contains id) (covered xs id)

theorem foldStacked: (acc: List Range) → (xs: List Range) →
    List.Sorted (a b => Ordering.isLessEq (Ord.compare a b)) xs → Fits acc xs → Stacked acc → Stacked (xs.foldLeft acc absorb)
  | acc, Nil, s, ok, st => st
  | acc, Cons x xs, Both hx sxs, ok, st => foldStacked (absorb acc x) xs sxs (fitsStep acc x xs ok hx) (absorbStacked x acc ok st)
