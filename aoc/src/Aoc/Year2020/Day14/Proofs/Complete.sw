--| The converse of `Parse.sw`: a program written out, a line to an
--| instruction, the first setting the mask, is read as that program.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14.Spec (InstructionWritten, MaskBitWritten, ProgramWritten, StartsWithMask)
import Std (Bool, Char, Eq, Exists, Fail, List, Parse, Result, Text, Void)

theorem runsMaskBit ∀ (read: List Char) (bit: MaskBit) (rest: List Char) (written: MaskBitWritten read bit): Parse.Runs maskBit read rest bit :=
  match bit with
    | Off => rewrite written in Parse.runsPick [] "0" Off [("1", On), ("X", X)] rest rfl
    | On => rewrite written in Parse.runsPick [("0", Off)] "1" On [("X", X)] rest (Both rfl rfl)
    | X => rewrite written in Parse.runsPick [("0", Off), ("1", On)] "X" X [] rest (Both rfl (Both rfl rfl))

theorem runsInstruction ∀ (read: List Char) (item: Instruction) (written: InstructionWritten read item): Parse.Runs instruction read [] item :=
  match item with
    | SetMask mask =>
      match mask with
        | { bits } =>
          match written with
            | Witness symbols (Both split (Both each count)) =>
              match Parse.eachSteps maskBit MaskBitWritten [] runsMaskBit bits symbols each with
                | Witness steps (Both joined (Both valued (Both counted stepsRun))) =>
                  rewrite split in
                    Parse.runsBind (() => Parse.optional (() => Parse.text "mask = ")) _ "mask = ".toList symbols _ [] (Some ()) _ rfl
                      (Parse.runsOptional (() => Parse.text "mask = ") "mask = ".toList (symbols ++ []) () (Parse.runsText "mask = " (symbols ++ [])))
                      (Parse.runsBind (() => Parse.exactly 36 maskBit) _ symbols [] symbols [] bits _ (Eq.sym (List.appendNil symbols))
                        (rewrite <- joined, <- valued in Parse.runsExactly 36 maskBit steps ([] ++ []) (Eq.trans counted count) stepsRun)
                        (Parse.runsPure (SetMask { bits }) []))
    | Write address value =>
      match written with
        | Witness addressRead (Witness valueRead (Both split (Both (Both aSome (Both aAll aValue)) (Both vSome (Both vAll vValue))))) =>
          rewrite split, aValue, vValue in
            Parse.runsBind (() => Parse.optional (() => Parse.text "mask = ")) _ [] ("mem[".toList ++ addressRead ++ "] = ".toList ++ valueRead) _ [] None _ rfl
              (Parse.declinesRuns (() => Parse.text "mask = ") _ (Parse.declinesText "mask = " _ rfl))
              (Parse.runsBind (() => Parse.text "mem[") _ "mem[".toList (addressRead ++ "] = ".toList ++ valueRead) _ [] () _ rfl
                (Parse.runsText "mem[" _)
                (Parse.runsBind Parse.nat _ addressRead ("] = ".toList ++ valueRead) _ [] (Parse.digitsValue addressRead) _ rfl
                  (Parse.runsNat addressRead _ aSome aAll rfl)
                  (Parse.runsBind (() => Parse.text "] = ") _ "] = ".toList valueRead _ [] () _ rfl
                    (Parse.runsText "] = " _)
                    (Parse.runsBind Parse.nat _ valueRead [] _ [] (Parse.digitsValue valueRead) _ (Eq.sym (List.appendNil valueRead))
                      (Parse.runsNat valueRead [] vSome vAll rfl)
                      (Parse.runsPure (Write (Parse.digitsValue addressRead) (Parse.digitsValue valueRead)) [])))))

theorem startsComplete ∀ (instructions: List Instruction) (starts: StartsWithMask instructions): startsWithMask instructions = True :=
  match instructions with
    | [SetMask mask, ..rest] => rfl

--| Input that is a program written out is read as that program.
theorem parseComplete ∀ (input: Text) (program: Program) (written: ProgramWritten (input.lines.map Text.toList) program):
    Fail.toResult (() => parseProgram input) = Ok program := match written with
      | Both lines starts =>
        let ran := Parse.runsEachLine input instruction program.instructions (List.all2Weaken runsInstruction _ _ lines)
        rewrite Fail.toResultThen (() => Parse.eachLine input instruction)
          (instructions => if startsWithMask instructions then ({ instructions }: Program) else Fail.fail "the program has to start with a mask") in
          rewrite ran, startsComplete program.instructions starts in
            match program with
              | { instructions } => rfl

--| A program is written by an input in at most one way, since the parser reads it as one.
theorem writtenUnique ∀ (input: Text) (a: Program) (b: Program) (writtenA: ProgramWritten (input.lines.map Text.toList) a)
    (writtenB: ProgramWritten (input.lines.map Text.toList) b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
