-- Day 3 without Std.Parse: one pass over the characters with prefix tests,
-- as the regex-free Haskell solutions do with `stripPrefix`.
namespace Scratch.Scan
import Std (Bool, IO, List, Nat, Option, Text)

-- One to three digits, then what follows them.
def number (value: Nat) (count: Nat): List Char → Option (Nat, List Char)
  | Cons char rest =>
    match char.digitValue with
      | Some digit => if count < 3 then number (value * 10 + digit) (count + 1) rest else None
      | None => if count == 0 then None else Some (value, Cons char rest)
  | Nil => None

-- The rest of a `mul` after "mul(": its product.
def mulArgs (chars: List Char): Option Nat :=
  match number 0 0 chars with
    | Some (left, Cons ',' afterComma) =>
      match number 0 0 afterComma with
        | Some (right, Cons ')' rest) => Some (left * right)
        | other => None
    | other => None

-- Both parts' sums, in one pass. After a match the scan goes on from the
-- next character, not from the match's end: nothing can start inside
-- `mul(1,2)`, `do()` or `don't()`, and recursing on `rest` is what the
-- termination checker accepts without fuel.
def scan (enabled: Bool) (part1: Nat) (part2: Nat): List Char → (Nat, Nat)
  | Nil => (part1, part2)
  | Cons char rest =>
    match Text.stripPrefixChars "mul(".toList (Cons char rest) with
      | Some afterMul =>
        match mulArgs afterMul with
          | Some product => scan enabled (part1 + product) (if enabled then part2 + product else part2) rest
          | None => scan enabled part1 part2 rest
      | None =>
        if Text.startsWithChars "do()".toList (Cons char rest) then scan True part1 part2 rest
        else if Text.startsWithChars "don't()".toList (Cons char rest) then scan False part1 part2 rest
        else scan enabled part1 part2 rest

def main(): {IO} () :=
  let (part1, part2) := scan True 0 0 IO.readAll().toList
  IO.print "Part 1: ${part1}"
  IO.print "Part 2: ${part2}"
