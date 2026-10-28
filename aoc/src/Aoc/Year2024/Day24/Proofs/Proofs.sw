-- Day 24 proved, for every device. Part 1: the number the program reads is
-- one the device outputs (`part1Sound`, Part1.sw), and for a well-formed
-- device (each wire with one source, as the puzzle says) it is the only one
-- and the program finds it (`part1Correct`, with Complete.sw and
-- Unique.sw). Part 2: gates of the ripple-carry shape add (`shapeAdds`,
-- Adder.sw, from the bit-by-bit sum in Sums.sw), and the swaps the answer
-- names, applied, give such gates, so the repaired device settles to x + y
-- for any x and y as wide as its x wires (`part2Correct`, Part2.sw). Not
-- proved: that no other swaps work (the puzzle promises one answer), or
-- that `repair` finds swaps whenever some exist. The parser isn't proved.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Aoc.Year2024.Day24.Spec (..)
import Std (Iff, Nat, Option)

-- Part 1 for a well-formed device: the program's number is the one the
-- device outputs, and it gives none when the device outputs none (when a z
-- wire gets no value, as in a loop).
theorem part1Correct (device: Device) (wellFormed: WellFormed device) (number: Nat): Iff (solvePart1 device = Some number) (Outputs device number) := {
  forward = solved => part1Sound device number solved,
  backward = outputs => part1Complete device wellFormed number outputs
}
