--| The converse of `Parse.sw`: a transmission of hexadecimal digits is read
--| as its bits, and its bits are the only ones it can be read as.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (hexDigitBits, transmissionBits)
import Std (Bool, Eq, Exists, Fail, List, Nat, Option, Parse, Result, Text, Void)

--| A character with bits in the puzzle's table is one the program reads, and
--| its bits are the program's.
theorem hexValueOf (char: Char) (bits: List Bool) (h: hexDigitBits char = Some bits): ∃ (value: Nat) => hexValue char = Some value ∧ bits = digitBits value :=
  match char with
    | '0' => Witness 0 (Both rfl (Eq.sym (Option.someInjective h)))
    | '1' => Witness 1 (Both rfl (Eq.sym (Option.someInjective h)))
    | '2' => Witness 2 (Both rfl (Eq.sym (Option.someInjective h)))
    | '3' => Witness 3 (Both rfl (Eq.sym (Option.someInjective h)))
    | '4' => Witness 4 (Both rfl (Eq.sym (Option.someInjective h)))
    | '5' => Witness 5 (Both rfl (Eq.sym (Option.someInjective h)))
    | '6' => Witness 6 (Both rfl (Eq.sym (Option.someInjective h)))
    | '7' => Witness 7 (Both rfl (Eq.sym (Option.someInjective h)))
    | '8' => Witness 8 (Both rfl (Eq.sym (Option.someInjective h)))
    | '9' => Witness 9 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'A' => Witness 10 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'B' => Witness 11 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'C' => Witness 12 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'D' => Witness 13 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'E' => Witness 14 (Both rfl (Eq.sym (Option.someInjective h)))
    | 'F' => Witness 15 (Both rfl (Eq.sym (Option.someInjective h)))
    | _ => cases

--| `hexDigit` on a digit, whatever follows.
theorem runsHexDigit (char: Char) (value: Nat) (rest: List Char) (found: hexValue char = Some value): Parse.Runs hexDigit [char] rest value :=
  Parse.runsBind (() => Parse.satisfy "a hexadecimal digit" (char => (hexValue char).isSome))
    (char => Parse.need (hexValue char) "expected a hexadecimal digit") [char] [] [char] rest char value (Eq.sym (List.appendNil [char]))
    (Parse.runsSatisfy _ _ char rest (rewrite found in rfl))
    (rewrite found in Parse.runsPure value rest)

--| `hexDigit` declines at the end of the input.
theorem declinesHexDigitEnd: Parse.Declines hexDigit [] :=
  Parse.declinesBind (() => Parse.satisfy "a hexadecimal digit" (char => (hexValue char).isSome))
    (char => Parse.need (hexValue char) "expected a hexadecimal digit") [] (Parse.declinesSatisfyEnd _ _)

--| The digits of a transmission with bits are read one by one, and give those
--| bits.
theorem runsDigits (chars: List Char) (bits: List Bool) (h: transmissionBits chars = Some bits):
    ∃ (steps: List (List Char, Nat)) => Parse.joinReads steps = chars ∧ Parse.ManyRuns hexDigit steps [] ∧ bitsOfDigits (Parse.stepValues steps) = bits :=
  match chars with
    | [] => Witness [] (Both rfl (Both declinesHexDigitEnd (Option.someInjective h)))
    | [char, ..rest] =>
      match digit: hexDigitBits char with
        | Some digitBits2 =>
          match later: transmissionBits rest with
            | Some more =>
              match hexValueOf char digitBits2 digit with
                | Witness value (Both found same) =>
                  match runsDigits rest more later with
                    | Witness steps (Both joined (Both manyRuns bitsSame)) =>
                      Witness [([char], value), ..steps]
                        (Both (rewrite joined in rfl)
                          (Both (Both (List.consNotNil char []) (Both (runsHexDigit char value (Parse.joinReads steps ++ []) found) manyRuns))
                            (rewrite <- Option.someInjective h, same, bitsSame in rfl)))

--| A transmission, trimmed, that the puzzle's table gives bits is read as
--| exactly those bits.
theorem parseComplete (input: Text) (bits: List Bool) (written: transmissionBits input.trim.toList = Some bits):
    Fail.toResult (() => readBits input) = Ok bits :=
  match runsDigits input.trim.toList bits written with
    | Witness steps (Both joined (Both manyRuns bitsSame)) =>
      let runs := Parse.runsMany hexDigit steps [] manyRuns
      let digits := rewrite joined at runs in
        Parse.runsLine input.trim (() => Parse.many hexDigit) (Parse.stepValues steps) (Parse.runsWithFinalLineBreakNone _ _ _ runs)
      rewrite Fail.toResultThen (() => readDigits input) (digits => bitsOfDigits digits), digits, bitsSame in rfl

--| A transmission is read as at most one list of bits: the table gives each
--| character bits, and the parser reads them back.
theorem writtenUnique (input: Text) (a: List Bool) (b: List Bool) (writtenA: transmissionBits input.trim.toList = Some a)
    (writtenB: transmissionBits input.trim.toList = Some b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
