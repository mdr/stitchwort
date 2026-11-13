--| Splitting a stone: the program divides by a power of 10 where the spec
--| takes the halves of the digit list. The halves recombine to the stone
--| (`recombine`), so the quotient and remainder are the halves (`splitLeft`,
--| `splitRight`) and the program changes each stone as the spec does
--| (`changeAgrees`). The left stone keeps all its digits (`leftStoneDigits`).

namespace Aoc.Year2024.Day11.Proofs
import Aoc.Year2024.Day11 (..)
import Aoc.Year2024.Day11.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| The stone is its left half shifted past the right half's digits, plus its
--| right half.
theorem recombine (stone: Nat) (half: Nat):
    Nat.fromDigits (stone.digits.toList.take half) * Nat.pow 10 (stone.digits.toList.drop half).length + Nat.fromDigits (stone.digits.toList.drop half)
      = stone :=
  rewrite <- Nat.fromDigitsAppend ((Nat.digits stone).toList.take half) ((Nat.digits stone).toList.drop half), List.appendTakeDrop (Nat.digits stone).toList half in
    Nat.fromDigitsDigits stone

--| With an even number of digits, the right half has half of them.
theorem rightHalfLength (stone: Nat) (even: stone.digitCount % 2 = 0):
    (stone.digits.toList.drop (stone.digitCount / 2)).length = stone.digitCount / 2 :=
  let split := List.lengthDrop (Nat.digits stone).toList (stone.digitCount / 2) (omega [Nat.digitCountLength stone])
  omega [split, even, Nat.digitCountLength stone]

--| The right half, as a number, is below 10 to the half.
theorem rightHalfSmall (stone: Nat) (even: stone.digitCount % 2 = 0):
    Nat.fromDigits (stone.digits.toList.drop (stone.digitCount / 2)) < Nat.pow 10 (stone.digitCount / 2) :=
  let right := (Nat.digits stone).toList.drop (stone.digitCount / 2)
  Nat.ltCongRight (Nat.fromDigits right) (Nat.pow 10 right.length) (Nat.pow 10 (stone.digitCount / 2)) (Eq.cong (Nat.pow 10) (rightHalfLength stone even))
    (Nat.fromDigitsBound right (Nat.digitsDrop (stone.digitCount / 2) (Nat.digits stone).toList (Nat.digitsDigits stone)))

--| `recombine`, with the right half's length as half the digits.
theorem recombineHalves (stone: Nat) (even: stone.digitCount % 2 = 0):
    stone
      = Nat.fromDigits (stone.digits.toList.take (stone.digitCount / 2)) * Nat.pow 10 (stone.digitCount / 2)
        + Nat.fromDigits (stone.digits.toList.drop (stone.digitCount / 2)) :=
  let half := stone.digitCount / 2
  Eq.trans (Eq.sym (recombine stone half))
    (Eq.cong (length => Nat.fromDigits ((Nat.digits stone).toList.take half) * Nat.pow 10 length + Nat.fromDigits ((Nat.digits stone).toList.drop half))
      (rightHalfLength stone even))

--| Dividing by 10 to the half gives the left half of the digits.
theorem splitLeft (stone: Nat) (even: stone.digitCount % 2 = 0):
    stone / Nat.pow 10 (stone.digitCount / 2) = Nat.fromDigits (stone.digits.toList.take (stone.digitCount / 2)) :=
  let half := stone.digitCount / 2
  Nat.divUnique stone (Nat.pow 10 half) (Nat.fromDigits ((Nat.digits stone).toList.take half))
    (Nat.fromDigits ((Nat.digits stone).toList.drop half)) (rightHalfSmall stone even) (recombineHalves stone even)

--| The remainder is the right half.
theorem splitRight (stone: Nat) (even: stone.digitCount % 2 = 0):
    stone % Nat.pow 10 (stone.digitCount / 2) = Nat.fromDigits (stone.digits.toList.drop (stone.digitCount / 2)) :=
  let half := stone.digitCount / 2
  Nat.modUnique stone (Nat.pow 10 half) (Nat.fromDigits ((Nat.digits stone).toList.take half))
    (Nat.fromDigits ((Nat.digits stone).toList.drop half)) (rightHalfSmall stone even) (recombineHalves stone even)

--| The program changes a stone as the puzzle says.
theorem changeAgrees (stone: Nat): changeStone stone = change stone :=
  match zero: stone == 0 with
    | True => rfl
    | False =>
      match even: stone.digitCount % 2 == 0 with
        | True =>
          let evenEq := even.read
          rewrite splitRight stone evenEq, splitLeft stone evenEq in rfl
        | False => rfl

--| A digit list starting with a digit other than 0 is the digits of its
--| number, and so is any non-empty start of it.
theorem digitsOfLeading (xs: List Nat) (count: Nat) (h: Nat.Digits xs) (lead: 1 ≤ xs.headOr 0) (some: 1 ≤ count):
    (Nat.digits (Nat.fromDigits (xs.take count))).toList = xs.take count :=
  match xs, count, h with
    | [first, ..rest], Succ count, Both small digits =>
      rewrite Nat.fromDigitsCons first (rest.take count), Nat.digitsShift (rest.take count) first lead (Nat.digitsTake count rest digits)
        in Eq.cong (l => List.append l (rest.take count)) (Eq.trans (Nat.digitsToList first) (Nat.digitsAccSmall first [] small))

--| The left stone shows exactly the left half of the digits: its first digit
--| isn't 0, so it loses none.
theorem leftStoneDigits (stone: Nat) (positive: 1 ≤ stone) (even: stone.digitCount % 2 = 0):
    (stone / Nat.pow 10 (stone.digitCount / 2)).digits.toList = stone.digits.toList.take (stone.digitCount / 2) :=
  rewrite splitLeft stone even in
    digitsOfLeading (Nat.digits stone).toList (stone.digitCount / 2) (Nat.digitsDigits stone) (Nat.digitsHead stone positive)
      (omega [Nat.digitCountPos stone, even])
