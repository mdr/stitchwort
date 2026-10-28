-- Day 11 proved: both parts count the stones of the puzzle's line, blinked
-- literally, for every line (`part1Correct`, `part2Correct`), from
-- `countCorrect`, which holds for any number of blinks (Counting.sw). Each
-- stone changes as the spec says (`changeAgrees`, Split.sw), and the order
-- of the line doesn't change the count (`countOrderIrrelevant`, Order.sw).

namespace Aoc.Year2024.Day11.Proofs
import Aoc.Year2024.Day11 (..)
import Aoc.Year2024.Day11.Spec (..)
import Std (List, Nat)

theorem part1Correct (stones: List Nat): solvePart1 stones = part1 stones := countCorrect 25 stones

theorem part2Correct (stones: List Nat): solvePart2 stones = part2 stones := countCorrect 75 stones
