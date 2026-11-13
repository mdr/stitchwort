--| Day 21 proved, about the input text: for every input the parser reads,
--| it is the foods written out (Parse.sw); when the program gives a part 2
--| answer, it is the canonical dangerous ingredient list, and the only one
--| (Part2.sw, with the elimination in `Aoc.Common.Proofs`); and part 1's
--| answer is the spec's count of the ingredients that can't contain an
--| allergen (Part1.sw), given some way the allergens could be in the
--| ingredients. The puzzle promises one; part 2's answer, when there is
--| one, provides it. Without one every ingredient trivially "can't
--| contain" an allergen, and the program's count would be wrong.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Aoc.Year2020.Day21 (Spec)
import Std (Eq, Fail, List, Option, Result, Text, Void)

--| Part 2's holders, when the elimination settles them, are a way the
--| allergens could be: the puzzle's promise, for part 1.
theorem promiseOfDangerous (list: FoodList) (answer: Text) (found: list.dangerousList = Some answer):
    ∃ (holder: Allergen → Ingredient) => Spec.Holding list holder := match settled: list.holders with
      | Some holders => Witness (list.holderOf holders) (holdersHolding list holders settled)

theorem part1Correct (input: Text) (list: FoodList) (parsed: Fail.toResult (() => parseFoods input) = Ok list)
    (promise: ∃ (holder: Allergen → Ingredient) => Spec.Holding list holder):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.FoodListWritten read list ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Part1 list list.safeAppearances :=
  Both (parseWritten input list parsed) (safeAppearancesSpec list promise)

--| Part 1 with no promise needed, once part 2 has an answer.
theorem part1Settled (input: Text) (list: FoodList) (parsed: Fail.toResult (() => parseFoods input) = Ok list) (answer: Text)
    (found: list.dangerousList = Some answer):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.FoodListWritten read list ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Part1 list list.safeAppearances :=
  part1Correct input list parsed (promiseOfDangerous list answer found)

theorem part2Correct (input: Text) (list: FoodList) (parsed: Fail.toResult (() => parseFoods input) = Ok list) (answer: Text)
    (found: list.dangerousList = Some answer):
    (∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Spec.FoodListWritten read list ∧ ending.all (char => char == '\n' ∨ char == '\r') = True)
      ∧ Spec.Part2 list answer ∧ (∀ (other: Text) => Spec.Part2 list other → other = answer) :=
  Both (parseWritten input list parsed) (Both (dangerousValid list answer found) (other => dangerousOnly list answer found other))
