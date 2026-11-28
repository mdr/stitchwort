--| The parser reads exactly the puzzle's format: if `parseProgram` reads
--| `input`, each line of it is its instruction written out, as
--| `Spec.InstructionWritten` says.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08.Spec (ArgumentWritten, InstructionWritten, OperationWritten)
import Std (Fail, List, Parse, Result, Text, Void)

theorem readsOperation: Parse.Reads operation OperationWritten :=
  Parse.readsWeaken (Parse.readsPickBy [Acc, Jmp, Nop] Operation.word) (read operation (Both member same) =>
    match operation with
      | Acc | Jmp => same
      | Nop => same)

theorem readsArgument: Parse.Reads Parse.int ArgumentWritten := Parse.readsInt

theorem readsInstruction: Parse.Reads instruction InstructionWritten :=
  Parse.readsThen readsOperation (operationRead operation written =>
    Parse.readsThen (Parse.readsChar ' ') (spaceRead u space =>
      Parse.readsThen readsArgument (argumentRead argument signed =>
        Parse.readsDone
          { operation, argument }
          (Witness operationRead
            (Witness argumentRead (Both (rewrite space, List.appendNil argumentRead) (Both written signed)))))))

--| If `parseProgram` reads `input`, each of its lines is an instruction written out.
theorem parseWritten ∀ (input: Text) (program: Program)
    (parsed: Fail.toResult (() => parseProgram input) = Ok program):
    List.All2 InstructionWritten (input.lines.map Text.toList) program.instructions :=
  let ran :=
    rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions =>
          ({ instructions }: Program)) at parsed then
      parsed
  match e: Fail.toResult (() => Parse.eachLine input instruction) with
    | Ok instructions =>
      rewrite <- Result.okInjective ran then
        Parse.eachLineReads input instruction InstructionWritten instructions e readsInstruction
