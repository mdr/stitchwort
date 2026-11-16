--| Day 2 proved: both of the program's checks are the puzzle's (Spec/), for
--| every entry, so both answers are the puzzle's for every list of entries.

namespace Aoc.Year2020.Day02.Proofs
import Aoc.Year2020.Day02 (..)
import Aoc.Year2020.Day02.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Text)

theorem validByCountSpec ∀ (entry: Entry): entry.validByCount = validPart1 entry :=
  rewrite List.lengthFilter entry.password.toList (== entry.letter) then byComputing

theorem part1Correct ∀ (entries: List Entry): solvePart1 entries = part1Answer entries :=
  rewrite List.lengthFilter entries validPart1 then List.countCongMem _ _ _ (e m => validByCountSpec e)

--| Characters numbered from `start` hold nothing at a position before `start`.
theorem holdsNothingBefore ∀ (letter: Char) (chars: List Char) (start position: Nat)
    (before: position < start):
    List.any (List.withIndexFrom start chars) (((at, char)) => at == position ∧ char == letter) = False :=
  match chars with
    | [] => byComputing
    | [c, ..rest] =>
      rewrite holdsNothingBefore letter rest (Succ start) position (Nat.lessLe position start before) then cases

--| Numbered from `start`, the character at `start + index` is the list's
--| `index`th, counting from 0.
theorem holdsGet ∀ (letter: Char) (chars: List Char) (start index position: Nat)
    (is: position = start + index):
    List.any (List.withIndexFrom start chars) (((at, char)) => at == position ∧ char == letter)
      = (List.get chars index == Some letter) :=
  match chars, index with
    | [], index => byComputing
    | [c, ..rest], Zero => rewrite holdsNothingBefore letter rest (Succ start) position arithmetic then cases
    | [c, ..rest], Succ index => rewrite holdsGet letter rest (Succ start) index position arithmetic then cases

theorem letterAtSpec ∀ (entry: Entry) (position: Nat): entry.letterAt position = holdsLetter entry position :=
  match position with
    | Zero => Eq.flipped (holdsNothingBefore entry.letter entry.password.toList 1 0 arithmetic)
    | Succ index => Eq.flipped (holdsGet entry.letter entry.password.toList 1 index (Succ index) byComputing)

--| "Exactly one of" two.
theorem exactlyOne ∀ (p: Nat → Bool) (x y: Nat): ((p x != p y): Bool) = (([x, y].filter p).length == 1) := cases

theorem validByPositionSpec ∀ (entry: Entry): entry.validByPosition = validPart2 entry :=
  rewrite letterAtSpec entry entry.low, letterAtSpec entry entry.high then
    exactlyOne (holdsLetter entry) entry.low entry.high

theorem part2Correct ∀ (entries: List Entry): solvePart2 entries = part2Answer entries :=
  rewrite List.lengthFilter entries validPart2 then List.countCongMem _ _ _ (e m => validByPositionSpec e)
