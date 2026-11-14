--| The parser reads exactly the puzzle's format: if `parseFoods` reads
--| `input`, the input is the foods written out, as `Spec.FoodListWritten`
--| says, then any line breaks.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Aoc.Year2020.Day21.Spec (
  AllergenWritten,
  CommaWritten,
  FoodListWritten,
  FoodWritten,
  IngredientWritten,
  LineBreakWritten
)
import Std (Char, Fail, List, NonEmptyList, Parse, Text)

theorem readsWord: Parse.Reads word (read taken =>
      read ≠ [] ∧ read.all Char.isAsciiLowercase = True ∧ taken = Text.fromList read) :=
  Parse.readsTakeWhile1

theorem readsIngredient: Parse.Reads ingredient IngredientWritten :=
  Parse.readsThen readsWord (nameRead name (Both named (Both letters made)) =>
    Parse.readsThen (Parse.readsChar ' ') (spaceRead u space =>
      Parse.readsDone { name } _ (rewrite made in Both (rewrite space in rfl) (Both named letters))))

theorem readsAllergen: Parse.Reads allergen AllergenWritten := Parse.readsThen readsWord (nameRead name (Both named
  (Both letters made)) =>
  Parse.readsDone { name } _ (rewrite made in Both (List.appendNil nameRead) (Both named letters)))

theorem readsFood: Parse.Reads food FoodWritten :=
  Parse.readsThen
    (Parse.readsMany1 ingredient IngredientWritten readsIngredient)
    (ingredientsRead ingredients ingredientsWritten =>
      Parse.readsThen (Parse.readsText "(contains ") (containsRead u contains =>
        Parse.readsThen
          (Parse.readsSepBy1 allergen
            (() => Parse.text ", ")
            AllergenWritten
            CommaWritten
            readsAllergen
            (Parse.readsText ", "))
          (allergensRead allergens allergensWritten =>
            Parse.readsThen (Parse.readsChar ')') (closeRead u2 close =>
              Parse.readsDone
                { ingredients = ingredients.toList, allergens = allergens.toList } _
                (Witness ingredientsRead
                  (Witness allergensRead
                    (Both
                      (rewrite contains, close in rfl)
                      (Both
                        (Witness ingredients (Both ingredientsWritten rfl))
                        (Witness allergens (Both allergensWritten rfl))))))))))

theorem readsFoodList: Parse.Reads foodList FoodListWritten :=
  Parse.readsThen (Parse.readsLines food FoodWritten readsFood) (foodsRead foods written =>
    Parse.readsDone { foods = foods.toList } _ (Witness foods (Both (rewrite List.appendNil foodsRead in written) rfl)))

theorem parseWritten ∀ (input: Text) (list: FoodList)
    (parsed: Fail.toResult (() => parseFoods input) = Ok list):
    ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
      ∧ FoodListWritten read list
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input Aoc.Year2020.Day21.foodList FoodListWritten list parsed readsFoodList
