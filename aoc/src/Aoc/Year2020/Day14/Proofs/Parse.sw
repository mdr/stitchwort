--| The parser reads exactly the puzzle's format: if `parseProgram` reads
--| `input`, each line of it is its instruction written out, as
--| `Spec.InstructionWritten` says, and the first sets the mask.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14.Spec (InstructionWritten, MaskBitWritten, ProgramWritten, StartsWithMask)
import Std (Bool, Char, Fail, List, Parse, Result, Text, Void)

theorem readsMaskBit: Parse.Reads maskBit MaskBitWritten :=
  Parse.readsWeaken (Parse.readsPickBy maskBits MaskBit.symbol)
    (read bit (Both member same) =>
      match bit with
        | Off => same
        | On => same
        | X => same)

theorem readsInstruction: Parse.Reads instruction InstructionWritten :=
  Parse.readsThen (Parse.readsOptional (Parse.readsText "mask = ")) (optionRead found maybe =>
    match found with
      | Some u =>
        Parse.readsThen (Parse.readsExactly 36 maskBit MaskBitWritten readsMaskBit) (symbols bits (Both each count) =>
          Parse.readsDone (SetMask { bits }) _ (Witness symbols (Both (rewrite maybe, List.appendNil symbols in rfl) (Both each count))))
      | None =>
        Parse.readsThen (Parse.readsText "mem[") (openRead u opened =>
          Parse.readsThen Parse.readsNat (addressRead address addressDecimal =>
            Parse.readsThen (Parse.readsText "] = ") (closeRead u closed =>
              Parse.readsThen Parse.readsNat (valueRead value valueDecimal =>
                Parse.readsDone (Write address value) _
                  (Witness addressRead (Witness valueRead
                    (Both (rewrite maybe, opened, closed, List.appendNil valueRead in rfl) (Both addressDecimal valueDecimal)))))))))

theorem startsWritten (instructions: List Instruction) (starts: startsWithMask instructions = True): StartsWithMask instructions :=
  match instructions with
    | [SetMask mask, ..rest] => Trivial

--| If `parseProgram` reads `input`, its lines are the program written out.
theorem parseWritten (input: Text) (program: Program) (parsed: Fail.toResult (() => parseProgram input) = Ok program):
    ProgramWritten (input.lines.map Text.toList) program :=
  let check := (instructions: List Instruction) =>
    if startsWithMask instructions then ({ instructions }: Program) else Fail.fail "the program has to start with a mask"
  let ran := rewrite Fail.toResultThen (() => Parse.eachLine input instruction) check at parsed in parsed
  match e: Fail.toResult (() => Parse.eachLine input instruction) with
    | Ok instructions =>
      match starts: startsWithMask instructions with
        | True =>
          rewrite <- Result.okInjective ran in
            Both (Parse.eachLineReads input instruction InstructionWritten instructions e readsInstruction) (startsWritten instructions starts)
