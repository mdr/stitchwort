--| The converse of `Parse.sw`: a program written out, a line to an
--| instruction, the first setting the mask, is read as that program.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14.Spec (InstructionWritten, MaskBitWritten, ProgramWritten, StartsWithMask)
import Std (Bool, Char, Eq, Exists, Fail, List, Parse, Result, Text, Void)

theorem runsMaskBit ∀ (read: List Char) (bit: MaskBit) (rest: List Char)
    (written: MaskBitWritten read bit):
    Parse.Runs maskBit read rest bit :=
  match bit with
    | Off => rewrite written then Parse.runsPick [] "0" Off [("1", On), ("X", X)] rest byComputing
    | On => rewrite written then Parse.runsPick [("0", Off)] "1" On [("X", X)] rest (Both byComputing byComputing)
    | X =>
      rewrite written then
        Parse.runsPick [("0", Off), ("1", On)] "X" X [] rest (Both byComputing (Both byComputing byComputing))

theorem runsInstruction ∀ (read: List Char) (item: Instruction)
    (written: InstructionWritten read item):
    Parse.Runs instruction read [] item :=
  match item with
    | SetMask mask =>
      match mask with
        | { bits } =>
          match written with
            | Witness symbols (Both split (Both each count)) =>
              match Parse.eachSteps maskBit MaskBitWritten [] runsMaskBit bits symbols each with
                | Witness steps (Both joined (Both valued (Both counted stepsRun))) =>
                  rewrite split then
                    Parse.runsBind
                      (() => Parse.optional (() => Parse.text "mask = ")) _
                      "mask = ".toList
                      symbols _
                      []
                      (Some ()) _
                      byComputing
                      (Parse.runsOptional
                        (() => Parse.text "mask = ")
                        "mask = ".toList
                        (symbols ++ [])
                        ()
                        (Parse.runsText "mask = " (symbols ++ [])))
                      (Parse.runsBind
                        (() => Parse.exactly 36 maskBit) _
                        symbols
                        []
                        symbols
                        []
                        bits _
                        (List.appendNil symbols).flipped
                        (rewrite <- joined, <- valued then
                          Parse.runsExactly 36 maskBit steps ([] ++ []) (Eq.trans counted count) stepsRun)
                        (Parse.runsPure (SetMask { bits }) []))
    | Write address value =>
      match written with
        | Witness addressRead
            (Witness valueRead (Both split (Both (Both aSome (Both aAll aValue)) (Both vSome (Both vAll vValue))))) =>
          rewrite split, aValue, vValue then
            Parse.runsBind
              (() => Parse.optional (() => Parse.text "mask = ")) _
              []
              ("mem[".toList ++ addressRead ++ "] = ".toList ++ valueRead) _
              []
              None _
              byComputing
              (Parse.declinesRuns (() => Parse.text "mask = ") _ (Parse.declinesText "mask = " _ byComputing))
              (Parse.runsBind
                (() => Parse.text "mem[") _
                "mem[".toList
                (addressRead ++ "] = ".toList ++ valueRead) _
                []
                () _
                byComputing
                (Parse.runsText "mem[" _)
                (Parse.runsBind Parse.nat _ addressRead
                  ("] = ".toList ++ valueRead) _
                  []
                  (Parse.digitsValue addressRead) _
                  byComputing
                  (Parse.runsNat addressRead _ aSome aAll byComputing)
                  (Parse.runsBind
                    (() => Parse.text "] = ") _
                    "] = ".toList
                    valueRead _
                    []
                    () _
                    byComputing
                    (Parse.runsText "] = " _)
                    (Parse.runsBind Parse.nat _ valueRead [] _ []
                      (Parse.digitsValue valueRead) _
                      (List.appendNil valueRead).flipped
                      (Parse.runsNat valueRead [] vSome vAll byComputing)
                      (Parse.runsPure (Write (Parse.digitsValue addressRead) (Parse.digitsValue valueRead)) [])))))

theorem startsComplete ∀ (instructions: List Instruction)
    (starts: StartsWithMask instructions):
    startsWithMask instructions = True :=
  match instructions with | [SetMask mask, ..rest] => byComputing

--| Input that is a program written out is read as that program.
theorem parseComplete ∀ (input: Text) (program: Program)
    (written: ProgramWritten (input.lines.map Text.toList) program):
    Fail.toResult (() => parseProgram input) = Ok program :=
  match written with
    | Both lines starts =>
      let ran := Parse.runsEachLine input instruction program.instructions (List.all2Weaken runsInstruction _ _ lines)
      rewrite Fail.toResultThen (() => Parse.eachLine input instruction) (instructions =>
            if startsWithMask instructions then ({ instructions }: Program)
            else Fail.fail "the program has to start with a mask"),
          ran,
          startsComplete program.instructions starts then
        match program with
          | { instructions } => byComputing

--| A program is written by an input in at most one way, since the parser reads it as one.
theorem writtenUnique ∀ (input: Text) (a b: Program)
    (writtenA: ProgramWritten (input.lines.map Text.toList) a)
    (writtenB: ProgramWritten (input.lines.map Text.toList) b):
    a = b :=
  Result.okInjective (Eq.trans (parseComplete input a writtenA).flipped (parseComplete input b writtenB))
