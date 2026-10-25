-- Day 7, part 2 counts timelines (`part2Correct`, Proofs/Part2.sw), and
-- the count is of different timelines: the spec's list has no repeats
-- (`timelinesDistinct`). By construction: the two sides of a split start
-- with the same splitter but a different turn, and each side is distinct
-- by induction. The library's `List.Distinct`, `List.distinctMap` with
-- `List.consInjective` (the timelines of one side all begin with the same
-- hit), and `List.distinctAppend` with `List.disjointMapCons` (the two
-- sides begin with different hits, so have nothing in common) do the work.

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Aoc.Day07.Spec (..)
import Std (DecEq, Decidable, Eq, Fin, List, Option, Vec)

-- Two hits at the same splitter that go different ways are different.
theorem turnsDiffer (r: Nat) (c: Nat): Not (({ row = r, column = c, turn = Left }: Hit) = { row = r, column = c, turn = Right }) :=
  p => Decidable.toBoolFalse (DecEq.decide (Left: Turn) Right) rfl (Eq.cong Hit.turn p)

-- The timelines of the two sides of a split.
theorem headsDistinct (h1: Hit) (h2: Hit) (ne: Not (h1 = h2)) (xs: List (List Hit)) (ys: List (List Hit))
    (dx: xs.Distinct) (dy: ys.Distinct):
    List.Distinct (List.append (List.map xs (Cons h1)) (List.map ys (Cons h2))) :=
  List.distinctAppend (List.map xs (Cons h1)) (List.map ys (Cons h2))
    (List.distinctMap xs dx (Cons h1) (List.consInjective h1))
    (List.distinctMap ys dy (Cons h2) (List.consInjective h2))
    (List.disjointMapCons ys h1 h2 ne xs)

-- Every timeline from a column is different from the others.
theorem timelinesFromDistinct (r: Nat) (c: Nat): (rows: List (Vec Bool w)) → List.Distinct (timelinesFrom r c rows)
  | Nil => Both (m => m) Trivial
  | Cons row rest =>
    match e: splitterAt row c with
      | True =>
        match c with
          | Zero =>
            headsDistinct { row = r, column = 0, turn = Left } { row = r, column = 0, turn = Right } (turnsDiffer r 0)
              [Nil] (timelinesFrom (r + 1) 1 rest) (Both (m => m) Trivial) (timelinesFromDistinct (r + 1) 1 rest)
          | Succ b =>
            headsDistinct { row = r, column = Succ b, turn = Left } { row = r, column = Succ b, turn = Right } (turnsDiffer r (Succ b))
              (timelinesFrom (r + 1) b rest) (timelinesFrom (r + 1) (Succ b + 1) rest)
              (timelinesFromDistinct (r + 1) b rest) (timelinesFromDistinct (r + 1) (Succ b + 1) rest)
      | False => timelinesFromDistinct (r + 1) c rest

-- No timeline of the particle from S is counted twice.
theorem timelinesDistinct (manifold: Manifold): List.Distinct (timelines manifold) :=
  timelinesFromDistinct 0 manifold.start.toNat manifold.rows

-- Both together: what part 2 prints is the length of the spec's list of
-- timelines, and that list has no repeats, so it is the number of different
-- timelines.
theorem part2Distinct (manifold: Manifold):
    solvePart2 manifold = List.length (timelines manifold) ∧ List.Distinct (timelines manifold) :=
  Both (part2Correct manifold) (timelinesDistinct manifold)
