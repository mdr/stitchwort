-- Day 9, part 1, proved for every list of red tiles (`part1Correct`): the
-- program's answer is the largest area of the spec's rectangles. The
-- program takes the areas of the same rectangles, so what is left is that
-- `largest` finds the largest (`largestIsLargest`), which part 2 uses too.

namespace Aoc.Year2025.Day09.Proofs
import Aoc.Year2025.Day09 (..)
import Aoc.Year2025.Day09.Spec (..)
import Std (List, Nat, Void)

-- `largest` is the largest of the areas, in the spec's sense.
theorem largestIsLargest (areas: List Nat): Largest areas (largest areas) :=
  Both (other m => List.leFoldMax areas other 0 m) (largestInList areas)

-- It is one of the areas, or 0 when there are none.
theorem largestInList: (areas: List Nat) → Or (List.Mem (largest areas) areas) (And (areas = Nil) (largest areas = 0))
  | Nil => Inr (Both rfl rfl)
  | Cons first rest =>
    match List.foldMaxMem (Cons first rest) 0 with
      | Inr m => Inl m
      -- The largest is 0, and the first area is at most that: 0 too.
      | Inl zero => Inl (Inl (omega [List.leFoldMax (Cons first rest) first 0 (Inl rfl)]))

theorem part1Correct (tiles: List Tile): Part1 tiles (solvePart1 tiles) := largestIsLargest (List.map (List.pairs tiles) pairArea)
