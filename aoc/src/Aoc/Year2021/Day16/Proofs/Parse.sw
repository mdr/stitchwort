--| The parser's guarantees: the input's characters are all hexadecimal
--| digits and the bits read are theirs.
-- (D2108)

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (hexDigitBits, transmissionBits)
import Std (Bool, Eq, Exists, Fail, List, Nat, Option, Parse, Result, Text, Void)

--| The program's digits are the puzzle's.
theorem hexAgree ∀ (char: Char) (value: Nat) (h: hexValue char = Some value): hexDigitBits char = Some (digitBits value) :=
  match char with
    | '0' => rewrite <- Option.someInjective h in rfl
    | '1' => rewrite <- Option.someInjective h in rfl
    | '2' => rewrite <- Option.someInjective h in rfl
    | '3' => rewrite <- Option.someInjective h in rfl
    | '4' => rewrite <- Option.someInjective h in rfl
    | '5' => rewrite <- Option.someInjective h in rfl
    | '6' => rewrite <- Option.someInjective h in rfl
    | '7' => rewrite <- Option.someInjective h in rfl
    | '8' => rewrite <- Option.someInjective h in rfl
    | '9' => rewrite <- Option.someInjective h in rfl
    | 'A' => rewrite <- Option.someInjective h in rfl
    | 'B' => rewrite <- Option.someInjective h in rfl
    | 'C' => rewrite <- Option.someInjective h in rfl
    | 'D' => rewrite <- Option.someInjective h in rfl
    | 'E' => rewrite <- Option.someInjective h in rfl
    | 'F' => rewrite <- Option.someInjective h in rfl

--| `hexDigit` reads one hexadecimal digit and gives its value.
theorem readsHexDigit: Parse.Reads hexDigit (read value => ∃ (char: Char) => read = [char] ∧ hexValue char = Some value) :=
  Parse.readsThen (Parse.readsSatisfy)
    (charRead char (Both one passes) =>
      Parse.readsWeaken (Parse.readsNeed (hexValue char) _) (read value (Both none found) =>
        Witness char (Both (rewrite one, none in rfl) found)))

--| Hexadecimal digits read one after another: their bits are the
--| transmission's.
theorem digitsBits ∀ (read: List Char) (values: List Nat)
    (none: Parse.Each (read value => ∃ (char: Char) => read = [char] ∧ hexValue char = Some value) read values): transmissionBits read = Some (bitsOfDigits values) :=
  match values, none with
    | [], none => rewrite none in rfl
    | [value, ..values], Witness first (Witness rest (Both split (Both (Witness char (Both one found)) others))) =>
      rewrite split, one, hexAgree char value found, digitsBits rest values others in rfl

--| The digits `readDigits` reads are the input's, all hexadecimal.
theorem readDigitsBits ∀ (input: Text) (values: List Nat) (read: Fail.toResult (() => readDigits input) = Ok values):
    transmissionBits input.trim.toList = Some (bitsOfDigits values) :=
  match Parse.lineReads input.trim (() => Parse.many hexDigit) _ values read (Parse.readsMany hexDigit _ readsHexDigit) with
    | Witness digits (Witness ending (Both split (Both each (Inl none)))) => rewrite split, none, List.appendNil digits in digitsBits digits values each
    | Witness digits (Witness ending (Both split (Both each (Inr (Inl newline))))) =>
      Void.exfalso (Bool.trueNotFalse (Text.trimLast input digits '\n' (rewrite split, newline in rfl)))
    | Witness digits (Witness ending (Both split (Both each (Inr (Inr crlf))))) =>
      Void.exfalso (Bool.trueNotFalse (Text.trimLast input (digits ++ ['\r']) '\n' (rewrite split, crlf, List.appendAssoc digits ['\r'] ['\n'] in rfl)))

--| The bits `readBits` reads are the transmission's.
theorem readBitsHex ∀ (input: Text) (bits: List Bool) (read: Fail.toResult (() => readBits input) = Ok bits): transmissionBits input.trim.toList = Some bits :=
  let split := rewrite Fail.toResultThen (() => readDigits input) (digits => bitsOfDigits digits) at read in read
  Result.flatMapEqOk (Fail.toResult (() => readDigits input)) (digits => Fail.toResult (() => bitsOfDigits digits)) bits split
    (values got made => rewrite <- Result.okInjective made in readDigitsBits input values got)
