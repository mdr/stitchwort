--| The parser reads exactly the puzzle's format: if `parseRoute` reads
--| `input`, each line of it is its instruction written out, as
--| `Spec.InstructionWritten` says.

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Common (Heading)
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12.Spec (ActionWritten, InstructionWritten)
import Std (Bool, Char, Fail, List, Parse, Result, Text, Void)

theorem readsAction: Parse.Reads action (read action => ∃ (letter: Char) => read = [letter] ∧ ActionWritten letter action) :=
  Parse.readsWeaken (Parse.readsPickBy actions Action.letter)
    (read action (Both member same) =>
      match action with
        | Move North => Witness 'N' (Both same rfl)
        | Move South => Witness 'S' (Both same rfl)
        | Move East => Witness 'E' (Both same rfl)
        | Move West => Witness 'W' (Both same rfl)
        | Turn Left => Witness 'L' (Both same rfl)
        | Turn Right => Witness 'R' (Both same rfl)
        | Forward => Witness 'F' (Both same rfl))

theorem readsInstruction: Parse.Reads instruction InstructionWritten :=
  Parse.readsThen readsAction (actionRead action (Witness letter (Both single written)) =>
    Parse.readsThen Parse.readsNat (digits value (Both nonEmpty (Both allDigits decimal)) =>
      match whole: action.isTurn && value % 90 != 0 with
        | True => Parse.readsFail "a turn has to be a multiple of 90 degrees" _
        | False =>
          Parse.readsDone { action, value } _
            (Witness letter (Witness digits
              (Both (rewrite single, List.appendNil digits in rfl)
                (Both written (Both nonEmpty (Both allDigits (Both decimal (turn => cases))))))))))

--| If `parseRoute` reads `input`, each of its lines is an instruction written out.
theorem parseWritten (input: Text) (route: Route) (parsed: Fail.toResult (() => parseRoute input) = Ok route):
    List.All2 InstructionWritten (input.lines.map Text.toList) route.instructions :=
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions => ({ instructions }: Route)) at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input instruction) with
    | Ok instructions => rewrite <- Result.okInjective ran in Parse.eachLineReads input instruction InstructionWritten instructions e readsInstruction
