--| Day 2 proved: both of the program's checks are the puzzle's (Spec/), for
--| every entry, so both answers are the puzzle's for every list of entries.

namespace Aoc.Year2020.Day02.Proofs
import Aoc.Year2020.Day02 (..)
import Aoc.Year2020.Day02.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)

theorem validByCountSpec ∀ (entry: Entry): entry.validByCount = validPart1 entry :=
  rewrite List.lengthFilter entry.password.toList (== entry.letter) in rfl

theorem part1Correct ∀ (entries: List Entry): solvePart1 entries = part1Answer entries :=
  rewrite List.lengthFilter entries validPart1 in List.countCongMem _ _ _ (e m => validByCountSpec e)

--| Characters numbered from `start` hold nothing at a position before `start`.
theorem holdsNothingBefore ∀ (letter: Char) (chars: List Char) (start position: Nat) (before: position < start):
    List.any (List.withIndexFrom start chars) (((at, char)) => at == position ∧ char == letter) = False :=
  match chars with
    | [] => rfl
    | [c, ..rest] =>
      rewrite holdsNothingBefore letter rest (Succ start) position (Nat.lessLe position start before) in cases

--| Numbered from `start`, the character at `start + index` is the list's
--| `index`th, counting from 0.
theorem holdsGet ∀ (letter: Char) (chars: List Char) (start index position: Nat) (is: position = start + index):
    List.any (List.withIndexFrom start chars) (((at, char)) => at == position ∧ char == letter) = (List.get chars index == Some letter) :=
  match chars, index with
    | [], index => rfl
    | [c, ..rest], Zero =>
      rewrite holdsNothingBefore letter rest (Succ start) position omega in cases
    | [c, ..rest], Succ index =>
      rewrite holdsGet letter rest (Succ start) index position omega in cases

theorem letterAtSpec ∀ (entry: Entry) (position: Nat): entry.letterAt position = holdsLetter entry position :=
  match position with
    | Zero => Eq.sym (holdsNothingBefore entry.letter entry.password.toList 1 0 omega)
    | Succ index => Eq.sym (holdsGet entry.letter entry.password.toList 1 index (Succ index) rfl)

--| "Exactly one of" two.
theorem exactlyOne ∀ (p: Nat → Bool) (x: Nat) (y: Nat): ((p x != p y): Bool) = (([x, y].filter p).length == 1) := cases

theorem validByPositionSpec ∀ (entry: Entry): entry.validByPosition = validPart2 entry :=
  rewrite letterAtSpec entry entry.low, letterAtSpec entry entry.high in exactlyOne (holdsLetter entry) entry.low entry.high

theorem part2Correct ∀ (entries: List Entry): solvePart2 entries = part2Answer entries :=
  rewrite List.lengthFilter entries validPart2 in List.countCongMem _ _ _ (e m => validByPositionSpec e)
