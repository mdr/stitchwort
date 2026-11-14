--| Day 14 proved, about the input text: for every input the parser reads,
--| its lines are the program written out and the first sets the mask
--| (Parse.sw); each part's answer is the spec's sum of memory after the
--| program, and no other number is (Parts.sw, with the mask in Bits.sw, the
--| decoder in Decode.sw, the memory in Memory.sw and the sum in Sum.sw).

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Eq, Fail, Result, Text)

theorem part1Correct ∀ (input: Text) (program: Program)
    (parsed: Fail.toResult (() => parseProgram input) = Ok program):
    Spec.ProgramWritten (input.lines.map Text.toList) program ∧ Spec.Part1 program program.valueSum :=
  Both (parseWritten input program parsed) (part1Rules program)

theorem part2Correct ∀ (input: Text) (program: Program)
    (parsed: Fail.toResult (() => parseProgram input) = Ok program):
    Spec.ProgramWritten (input.lines.map Text.toList) program ∧ Spec.Part2 program program.decodedSum :=
  Both (parseWritten input program parsed) (part2Rules program)

--| Part 1's answer is the spec's sum, and no other number is. It holds for
--| any program, parsed or not.
theorem part1Exactly ∀ (program: Program) (answer: Nat): program.valueSum = answer ↔ Spec.Part1 program answer := {
  forward = same => rewrite <- same in part1Rules program,
  backward = sums =>
    sumOfMemoryUnique (Spec.run Spec.writeMasked program) program.valueSum answer (part1Rules program) sums
}

--| Part 2's answer is the spec's sum, and no other number is.
theorem part2Exactly ∀ (program: Program) (answer: Nat): program.decodedSum = answer ↔ Spec.Part2 program answer := {
  forward = same => rewrite <- same in part2Rules program,
  backward = sums =>
    sumOfMemoryUnique (Spec.run Spec.writeDecoded program) program.decodedSum answer (part2Rules program) sums
}
