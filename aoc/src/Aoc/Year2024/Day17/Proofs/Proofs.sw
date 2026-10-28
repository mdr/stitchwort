-- Day 17 proved, for every program and every initial register values:
--
-- Steps (Step.sw): each step the program takes is the one the puzzle
-- describes (`stepMatches`): every opcode, every operand, the halt past the
-- end of the program, and XOR as the puzzle's bitwise XOR.
--
-- Runs (Run.sw): a run that finishes is a halting run of the puzzle's
-- computer with the same output (`outcomeHalts`), and more fuel finishes
-- the same way (`runMoreFuel`). So part 1's answer is what the program
-- outputs.
--
-- Part 2 (Search.sw): what the search returns is positive and the program,
-- started with it in A, halts having output itself (`part2Sound`). If what
-- the program outputs has the loop shape (`LoopShape`), the search finds a
-- value whenever a positive one outputs the program (`part2Complete`), and
-- returns the least (`part2Least`).
--
-- Not proved: that a halting run of the puzzle's computer finishes within
-- the program's fuel, so that `part2Least` covers every value the puzzle
-- counts; and that any particular program has the loop shape.
-- NOTES-2024.md says why.

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (And, Eq, Exists, List, Nat, Option, Void)

-- Part 1: the output of a finished run is a halting run's.
theorem part1Halts (debugger: Debugger) (output: List Nat) (finished: outcome debugger.registers debugger.program = Finished output):
    Halts debugger.program (start debugger.registers) output :=
  outcomeHalts debugger.registers debugger.program output finished

-- No positive value outputs nothing.
theorem lowestNil (output: Nat → List Nat): lowestOutputting output Nil = None := rfl

-- Part 2: the value found is positive, and outputs the program.
theorem part2Sound (debugger: Debugger) (a: Nat) (found: solvePart2 debugger = Some a): And (0 < a) (OutputsItself debugger a) :=
  let facts := lowestSound debugger.outputFor debugger.program a found
  match finished: outcome { debugger.registers | a } debugger.program with
    | Finished output => Both (And.left facts) (rewrite And.right facts at outcomeHalts { debugger.registers | a } debugger.program output finished)
    | Faulted => Void.exfalso (Option.noneNotSome a (rewrite Eq.sym (And.right facts), lowestNil debugger.outputFor at found))
    | OutOfFuel => Void.exfalso (Option.noneNotSome a (rewrite Eq.sym (And.right facts), lowestNil debugger.outputFor at found))

-- Part 2, for a program whose output has the loop shape: the value found
-- is at most any positive value whose run outputs the program.
theorem part2Least (debugger: Debugger) (shape: LoopShape debugger.outputFor) (a: Nat) (found: solvePart2 debugger = Some a) (other: Nat)
    (positive: 0 < other) (outputs: debugger.outputFor other = debugger.program): a ≤ other :=
  lowestLeast debugger.outputFor shape debugger.program a found other positive outputs

-- And a value is found if there is one.
theorem part2Complete (debugger: Debugger) (shape: LoopShape debugger.outputFor) (other: Nat) (positive: 0 < other)
    (outputs: debugger.outputFor other = debugger.program): ∃ (a: Nat) => solvePart2 debugger = Some a :=
  lowestComplete debugger.outputFor shape debugger.program other positive outputs

