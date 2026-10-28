-- Day 13 proved: part 1 is the spec's for every list of machines
-- (`part1Correct`, from `withinCorrect` in Part1.sw); part 2 is the spec's
-- for machines whose buttons don't move the claw along the same line
-- (`part2Correct`, from `fewestTokensCorrect` in Part2.sw). Both rest on
-- Cramer's rule finding exactly the presses that win (Cramer.sw).

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day13 (..)
import Aoc.Year2024.Day13.Spec (Part2Answer, part1)
import Std (And, Eq, Exists, List, Option)

theorem part1Correct (machines: List Machine): solvePart1 machines = part1 machines :=
  List.sumByCong machines _ _ (machine => Eq.cong (result => Option.getOrElse result 0) (withinCorrect machine))

-- The puzzle doesn't rule out buttons along the same line; this assumes
-- every machine's buttons aren't.
theorem part2Correct (machines: List Machine) (nonzero: (machine: Machine) → machine ∈ machines → machine.determinant ≠ 0):
    Part2Answer machines (solvePart2 machines) :=
  Witness (machine => machine.corrected.fewestTokens)
    (Both (machine member => rewrite <- correctedIsSpec machine in fewestTokensCorrect machine.corrected (nonzero machine member)) rfl)
