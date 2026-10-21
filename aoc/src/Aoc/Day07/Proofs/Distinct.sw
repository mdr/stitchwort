-- Day 7, part 2 counts timelines (`part2Correct`, Proofs/Part2.sw), and
-- the count is of different timelines: the spec's list has no repeats
-- (`timelinesDistinct`). By construction: the two sides of a split start
-- with the same splitter but a different turn, and each side is distinct
-- by induction. The library's `List.Distinct`, `List.distinctMap` (the
-- timelines of one side all begin with the same hit, which is injective)
-- and `List.distinctAppend` (two sides with nothing in common) do the work.

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Eq)

def Turn.isLeft: Turn -> Bool
  | Left  => True
  | Right => False

-- Two hits at the same splitter that go different ways are different.
theorem turnsDiffer (r: Nat) (c: Nat): Not (({ row = r, column = c, turn = Left }: Hit) = { row = r, column = c, turn = Right }) :=
  p => Bool.falseNotTrue (Eq.sym (Eq.cong (h => Turn.isLeft (Hit.turn h)) p))

-- Putting the same hit in front of two timelines gives different ones only
-- if the tails were.
theorem consInjective (h: Hit) (x: List Hit) (y: List Hit) (p: Cons h x = Cons h y): x = y := Eq.cong (List.drop 1) p

-- A timeline that starts with one hit isn't among those that start with
-- another.
theorem notMemHeads (h1: Hit) (h2: Hit) (ne: Not (h1 = h2)) (x: List Hit):
    (ys: List (List Hit)) -> Not (List.Mem (Cons h1 x) (List.map (Cons h2) ys))
  | Nil,       m => m
  | Cons y ys, m =>
    match m with
      | Inl p => ne (Eq.sym (Eq.cong (List.headOr h1) p))
      | Inr q => notMemHeads h1 h2 ne x ys q

theorem disjointHeads (h1: Hit) (h2: Hit) (ne: Not (h1 = h2)) (ys: List (List Hit)):
    (xs: List (List Hit)) -> List.Disjoint (List.map (Cons h1) xs) (List.map (Cons h2) ys)
  | Nil       => Trivial
  | Cons x xs => Both (notMemHeads h1 h2 ne x ys) (disjointHeads h1 h2 ne ys xs)

-- The timelines of the two sides of a split.
theorem headsDistinct (h1: Hit) (h2: Hit) (ne: Not (h1 = h2)) (xs: List (List Hit)) (ys: List (List Hit))
    (dx: List.Distinct xs) (dy: List.Distinct ys):
    List.Distinct (List.append (List.map (Cons h1) xs) (List.map (Cons h2) ys)) :=
  List.distinctAppend (List.map (Cons h1) xs) (List.map (Cons h2) ys)
    (List.distinctMap (Cons h1) (consInjective h1) xs dx)
    (List.distinctMap (Cons h2) (consInjective h2) ys dy)
    (disjointHeads h1 h2 ne ys xs)

-- Every timeline from a column is different from the others.
theorem timelinesFromDistinct (r: Nat) (c: Nat): (lines: List Text) -> List.Distinct (timelinesFrom r c lines)
  | Nil            => Both (m => m) Trivial
  | Cons line rest =>
    match e: charAt line c == '^' with
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

-- No timeline of the particle from S is counted twice: the number part 2
-- prints is the number of different timelines.
def TimelinesDistinct: Maybe (List (List Hit)) -> Prop
  | Nothing => Unit
  | Just ts => List.Distinct ts

theorem timelinesDistinct (lines: List Text): TimelinesDistinct (timelines lines) :=
  match e: findStart lines with
    | Nothing           => Trivial
    | Just (MkPair r c) => timelinesFromDistinct (r + 1) c (List.drop (r + 1) lines)

-- Both together: what part 2 prints is the length of the spec's list of
-- timelines, and that list has no repeats, so it is the number of different
-- timelines.
def CountsDistinct (answer: Maybe Nat): Maybe (List (List Hit)) -> Prop
  | Nothing => answer = Nothing
  | Just ts => And (answer = Just (List.length ts)) (List.Distinct ts)

theorem part2Distinct (lines: List Text): CountsDistinct (Maybe.map solvePart2 (parseManifold lines)) (timelines lines) :=
  match e: findStart lines with
    | Nothing           => rfl
    | Just (MkPair r c) =>
      Both (Eq.cong Just (countsAre (gridWidth lines) (List.drop (r + 1) lines) (belowFits lines r) (r + 1) c))
           (timelinesFromDistinct (r + 1) c (List.drop (r + 1) lines))
