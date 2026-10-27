-- Day 1, part 2 as the puzzle states it: turn the dial one click at a time, and
-- count the positions after each click that are 0. The proofs (Proofs/Part2.sw)
-- and the tests (Tests/Spec.sw) compare the program's arithmetic count with it.

namespace Aoc.Year2025.Day01.Spec
import Aoc.Year2025.Day01 (..)
import Std (List, Nat)

-- The specification of part 2: turn the dial one click at a time, and count
-- the positions after each click that are 0.
def zerosPassedSpec (turns: List Turn) (startingDial: Dial n): Nat :=
  turns |> .concatMap Turn.clicks |> zerosLandedOn startingDial
