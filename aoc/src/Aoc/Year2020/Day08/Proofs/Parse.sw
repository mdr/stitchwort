--| The parser reads exactly the puzzle's format: if `parseProgram` reads
--| `input`, each line of it is its instruction written out, as
--| `Spec.InstructionWritten` says.

namespace Aoc.Year2020.Day08.Proofs
import Aoc.Year2020.Day08 (..)
import Aoc.Year2020.Day08.Spec (ArgumentWritten, InstructionWritten, OperationWritten)
import Std (Fail, Int, List, Pair, Parse, Result, Text, Void)

theorem readsOperation: Parse.Reads operation OperationWritten :=
  Parse.readsWeaken (Parse.readsPickBy [Acc, Jmp, Nop] Operation.word)
    (read operation (Both member same) =>
      match operation with
        | Acc => same
        | Jmp => same
        | Nop => same)

theorem readsArgument: Parse.Reads argument ArgumentWritten :=
  Parse.readsThen (Parse.readsPick [("+", False), ("-", True)]) (signRead negative (Witness word (Both member signIs)) =>
    Parse.readsThen Parse.readsNat (digitsRead size (Both nonEmpty (Both digits value)) =>
      Parse.readsDone (Int.signed negative size) (read made => ArgumentWritten (signRead ++ (digitsRead ++ read)) made)
        (Witness digitsRead (Both nonEmpty (Both digits
          (match member with
            | Inl same =>
              rewrite signIs, <- Pair.mkInjectiveFst same, <- Pair.mkInjectiveSnd same, value, List.appendNil digitsRead in Inl (Both rfl rfl)
            | Inr (Inl same) =>
              rewrite signIs, <- Pair.mkInjectiveFst same, <- Pair.mkInjectiveSnd same, value, List.appendNil digitsRead in Inr (Both rfl rfl)
            | Inr (Inr none) => Void.exfalso none))))))

theorem readsInstruction: Parse.Reads instruction InstructionWritten :=
  Parse.readsThen readsOperation (operationRead operation written =>
    Parse.readsThen (Parse.readsChar ' ') (spaceRead u space =>
      Parse.readsThen readsArgument (argumentRead argument signed =>
        Parse.readsDone { operation, argument } (read made => InstructionWritten (operationRead ++ (spaceRead ++ (argumentRead ++ read))) made)
          (Witness operationRead (Witness argumentRead
            (Both (rewrite space, List.appendNil argumentRead in rfl) (Both written signed)))))))

--| If `parseProgram` reads `input`, each of its lines is an instruction written out.
theorem parseWritten (input: Text) (program: Program) (parsed: Fail.toResult (() => parseProgram input) = Ok program):
    List.All2 InstructionWritten (input.lines.map Text.toList) program.instructions :=
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions => ({ instructions }: Program)) at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input instruction) with
    | Ok instructions => rewrite <- Result.okInjective ran in Parse.eachLineReads input instruction InstructionWritten instructions e readsInstruction
    | Err message => Void.exfalso (Result.errNotOk ran)
