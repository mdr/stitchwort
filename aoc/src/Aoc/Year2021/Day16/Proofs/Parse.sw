--| The parser's guarantees: the input's characters are all hexadecimal
--| digits and the bits read are theirs; the packet read is well formed,
--| its encoding starts those bits, and its operators keep the puzzle's
--| promise.
-- (D2108)

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allPromised, encode, fitsOperation, hexDigitBits, promised, transmissionBits, wellFormed)
import Std (Bool, Eq, Exists, Fail, List, Nat, Option, Parse, Result, Text, Void)

--| The program's digits are the puzzle's.
theorem hexAgree (char: Char) (value: Nat) (h: hexValue char = Some value): hexDigitBits char = Some (digitBits value) :=
  match char with
    | '0' => rewrite <- Option.someInjective _ value h in rfl
    | '1' => rewrite <- Option.someInjective _ value h in rfl
    | '2' => rewrite <- Option.someInjective _ value h in rfl
    | '3' => rewrite <- Option.someInjective _ value h in rfl
    | '4' => rewrite <- Option.someInjective _ value h in rfl
    | '5' => rewrite <- Option.someInjective _ value h in rfl
    | '6' => rewrite <- Option.someInjective _ value h in rfl
    | '7' => rewrite <- Option.someInjective _ value h in rfl
    | '8' => rewrite <- Option.someInjective _ value h in rfl
    | '9' => rewrite <- Option.someInjective _ value h in rfl
    | 'A' => rewrite <- Option.someInjective _ value h in rfl
    | 'B' => rewrite <- Option.someInjective _ value h in rfl
    | 'C' => rewrite <- Option.someInjective _ value h in rfl
    | 'D' => rewrite <- Option.someInjective _ value h in rfl
    | 'E' => rewrite <- Option.someInjective _ value h in rfl
    | 'F' => rewrite <- Option.someInjective _ value h in rfl
    | _ => cases

--| `hexDigit` reads one hexadecimal digit and gives its value.
theorem readsHexDigit: Parse.Reads hexDigit (read value => ∃ (char: Char) => read = [char] ∧ hexValue char = Some value) :=
  Parse.readsThen (() => Parse.satisfy "a hexadecimal digit" (char => (hexValue char).isSome)) _ _ _
    (Parse.readsSatisfy _ _)
    (charRead char (Both one passes) =>
      Parse.readsWeaken _ _ _ (Parse.readsNeed (hexValue char) _) (read value (Both none found) =>
        Witness char (Both (rewrite one, none in rfl) found)))

--| Hexadecimal digits read one after another: their bits are the
--| transmission's.
theorem digitsBits: (read: List Char) → (values: List Nat) →
    Parse.Each (read value => ∃ (char: Char) => read = [char] ∧ hexValue char = Some value) read values → transmissionBits read = Some (bitsOfDigits values)
  | read, Nil, none => rewrite none in rfl
  | read, Cons value values, Witness first (Witness rest (Both split (Both (Witness char (Both one found)) others))) =>
    rewrite split, one, hexAgree char value found, digitsBits rest values others in rfl

--| The digits `readDigits` reads are the input's, all hexadecimal.
theorem readDigitsBits (input: Text) (values: List Nat) (read: Fail.toResult (() => readDigits input) = Ok values):
    transmissionBits input.trim.toList = Some (bitsOfDigits values) :=
  match Parse.lineReads input.trim (() => Parse.many hexDigit) _ values read (Parse.readsMany hexDigit _ readsHexDigit) with
    | Witness digits (Witness ending (Both split (Both each (Inl none)))) => rewrite split, none, List.appendNil digits in digitsBits digits values each
    | Witness digits (Witness ending (Both split (Both each (Inr (Inl newline))))) =>
      Void.exfalso (Bool.trueNotFalse (Text.trimLast input digits '\n' (rewrite split, newline in rfl)))
    | Witness digits (Witness ending (Both split (Both each (Inr (Inr crlf))))) =>
      Void.exfalso (Bool.trueNotFalse (Text.trimLast input (digits ++ ['\r']) '\n' (rewrite split, crlf, List.appendAssoc digits ['\r'] ['\n'] in rfl)))

--| The bits `readBits` reads are the transmission's.
theorem readBitsHex (input: Text) (bits: List Bool) (read: Fail.toResult (() => readBits input) = Ok bits): transmissionBits input.trim.toList = Some bits :=
  let split := rewrite Fail.toResultThen (() => readDigits input) (digits => bitsOfDigits digits) at read in read
  Result.flatMapEqOk (Fail.toResult (() => readDigits input)) (digits => Fail.toResult (() => bitsOfDigits digits)) bits split
    (values got made => rewrite <- Result.okInjective _ bits made in readDigitsBits input values got)

--| The program's check of an operator's sub-packets is the spec's.
theorem fitsAgree (operation: Operation) (count: Nat): fitsArity count (arity operation) = fitsOperation operation count :=
  match operation, count with
    | Minimum, 0 => rfl
    | Minimum, Succ _ => rfl
    | Maximum, 0 => rfl
    | Maximum, Succ _ => rfl
    | Sum, _ => rfl
    | Product, _ => rfl
    | GreaterThan, _ => rfl
    | LessThan, _ => rfl
    | EqualTo, _ => rfl

--| An operator the check finds nothing wrong with keeps the promise.
theorem badOperatorNone: (packet: Packet) → badOperator packet = None → promised packet = True
  | Literal _ _, none => rfl
  | Operator version operation lengthType subPackets, none =>
    match f: fitsArity subPackets.length (arity operation) with
      | True => Bool.andIntro _ _ (rewrite <- fitsAgree operation subPackets.length in f) (badOperatorInNone subPackets none)
      | False => cases

theorem badOperatorInNone: (packets: List Packet) → badOperatorIn packets = None → allPromised packets = True
  | Nil, none => rfl
  | Cons packet rest, none =>
    match b: badOperator packet with
      | None => Bool.andIntro _ _ (badOperatorNone packet b) (badOperatorInNone rest none)
      | Some _ => cases
