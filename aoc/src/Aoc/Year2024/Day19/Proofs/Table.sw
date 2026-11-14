--| The program's table holds, for each suffix, the number of towel lists
--| that make it (`tableCorrect`): entry `index` is the suffix after `index`
--| stripes, made by lists of any length up to `count`, once `count` is at
--| least the suffix's length. So the table's first entry is the spec's
--| number of ways (`waysCorrect`).

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

theorem tableCorrect ∀ (patterns: List Pattern):
    ∀ (stripes: List Stripe) (index: Nat) => index ≤ stripes.length
      → ∀ (count: Nat) => stripes.length - index ≤ count
        → (waysForSuffixes patterns stripes).getOr index 0 = matching patterns count (stripes.drop index)
  | [], Zero, inside, count, enough => Eq.sym (matchingEmpty patterns count)
  | [], Succ index, inside, count, enough => Void.exfalso (omega [inside])
  | [first, ..rest], Succ index, inside, count, enough =>
    tableCorrect patterns rest index (omega [inside]) count (omega [enough])
  | [first, ..rest], Zero, inside, Zero, enough => Void.exfalso (omega [enough])
  | [first, ..rest], Zero, inside, Succ count, enough =>
    rewrite matchingSucc patterns count [first, ..rest] in
      List.sumByCongMem patterns
        (pattern =>
          if [first, ..rest].startsWith pattern.stripes.toList then
            (waysForSuffixes patterns rest).getOr (pattern.length - 1) 0
          else 0)
        (pattern =>
          if [first, ..rest].startsWith pattern.stripes.toList then
            matching patterns count ([first, ..rest].drop pattern.stripes.toList.length)
          else 0)
        (pattern member =>
          match starts: [first, ..rest].startsWith pattern.stripes.toList with
            | True =>
              tableCorrect patterns rest pattern.stripes.tail.length
                (omega [List.startsWithLength [first, ..rest] pattern.stripes.toList starts])
                count
                (omega [enough])
            | False => rfl)

--| The table's first entry is its entry 0.
theorem firstEntry ∀ (patterns: List Pattern) (stripes: List Stripe):
    (waysForSuffixes patterns stripes).headOr 0 = (waysForSuffixes patterns stripes).getOr 0 0 :=
  match stripes with
    | [] => rfl
    | [first, ..rest] => rfl

--| The program counts the puzzle's ways to make any design.
theorem waysCorrect ∀ (patterns: List Pattern) (design: Design): waysToMake patterns design = ways patterns design :=
  rewrite List.lengthFilter (towelLists patterns design.stripes.length) (towels => laid towels == design.stripes),
      firstEntry patterns design.stripes in
    tableCorrect patterns design.stripes 0 (omega) design.stripes.length (omega)
