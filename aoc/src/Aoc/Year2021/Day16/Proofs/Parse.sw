-- The parser's guarantees (D2108): the input's characters are all
-- hexadecimal digits and the bits read are theirs; the packet read is well
-- formed, its encoding starts those bits, and its operators keep the
-- puzzle's promise.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (allPromised, encode, fitsOperation, hexDigitBits, promised, transmissionBits, wellFormed)
import Std (Bool, Eq, Exists, Fail, List, Nat, Option, Result, Text, Void)

-- The program's digits are the puzzle's.
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

-- Characters read one by one as digits, by any reader that reads only a
-- hexadecimal digit's value: their bits are the transmission's.
theorem digitsRead (f: (Nat, Char) → Result Nat Text) (agree: (entry: (Nat, Char)) → (value: Nat) → f entry = Ok value → hexValue entry.snd = Some value):
    (start: Nat) → (chars: List Char) → (values: List Nat) → Result.traverse (List.withIndexFrom start chars) f = Ok values → transmissionBits chars = Some (bitsOfDigits values)
  | start, Nil, values, done => rewrite <- Result.okInjective Nil values done in rfl
  | start, Cons char rest, values, done =>
    Result.flatMapEqOk (f (start, char)) (y => Result.map (Result.traverse (List.withIndexFrom (Succ start) rest) f) (Cons y)) values
      (rewrite Result.traverseCons f (start, char) (List.withIndexFrom (Succ start) rest) at done in done)
      (value first later =>
        match e: Result.traverse (List.withIndexFrom (Succ start) rest) f with
          | Err m => Void.exfalso (Result.errNotOk m values later)
          | Ok others =>
            rewrite <- Result.okInjective (Cons value others) values later, hexAgree char value (agree (start, char) value first), digitsRead f agree (Succ start) rest others e in rfl)

-- A character `need` reads as a digit is one.
theorem charRead (msg: Text) (char: Char) (value: Nat) (found: Option.toResult (hexValue char) msg = Ok value): hexValue char = Some value :=
  match e: hexValue char with
    | None => Void.exfalso (Result.errNotOk _ value found)
    | Some read => rewrite Result.okInjective read value found in rfl

-- The digits `readDigits` reads are the input's, all hexadecimal.
theorem readDigitsBits (input: Text) (values: List Nat) (read: Fail.toResult (() => readDigits input) = Ok values):
    transmissionBits input.trim.toList = Some (bitsOfDigits values) :=
  let traversed := rewrite Fail.toResultMap _ (input.trim.toList.withIndex) at read in read
  digitsRead _
    (entry value found =>
      match entry with
        | (column, char) => charRead _ char value (rewrite Fail.toResultNeed _ (hexValue char) at found in found))
    0 input.trim.toList values traversed

-- The bits `readBits` reads are the transmission's.
theorem readBitsHex (input: Text) (bits: List Bool) (read: Fail.toResult (() => readBits input) = Ok bits): transmissionBits input.trim.toList = Some bits :=
  let split := rewrite Fail.toResultThen (() => readDigits input) (digits => bitsOfDigits digits) at read in read
  Result.flatMapEqOk (Fail.toResult (() => readDigits input)) (digits => Fail.toResult (() => bitsOfDigits digits)) bits split
    (values got made => rewrite <- Result.okInjective _ bits made in readDigitsBits input values got)

-- The program's check of an operator's sub-packets is the spec's.
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

-- An operator the check finds nothing wrong with keeps the promise.
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
