--| Day 8 proved, about the input text: for every input the parser reads,
--| its lines are the instructions written out (Parse.sw); part 1 is the
--| accumulator of a run from the start that is about to execute an
--| instruction for the second time, having executed none twice (Run.sw,
--| Part1.sw); and part 2 is the accumulator of the boot code, with one
--| `jmp` or `nop` repaired, when it terminates (Part2.sw).

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08 (Spec)
import Std (Fail, Int, List, Result, Text)

theorem part1Correct ∀ (input: Text) (program: Program)
    (parsed: Fail.toResult (() => parseProgram input) = Ok program) (answer: Int)
    (solved: Fail.toResult (() => solvePart1 program) = Ok answer):
    List.All2 Spec.InstructionWritten (input.lines.map Text.toList) program.instructions ∧ Spec.Part1 program answer :=
  Both (parseWritten input program parsed) (part1Rules program answer solved)

theorem part2Correct ∀ (input: Text) (program: Program)
    (parsed: Fail.toResult (() => parseProgram input) = Ok program) (answer: Int)
    (solved: Fail.toResult (() => solvePart2 program) = Ok answer):
    List.All2 Spec.InstructionWritten (input.lines.map Text.toList) program.instructions ∧ Spec.Part2 program answer :=
  Both (parseWritten input program parsed) (part2Rules program answer solved)
