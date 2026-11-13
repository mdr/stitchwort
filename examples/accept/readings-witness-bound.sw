-- A fact bound by a `Witness` pattern reads as what its test says, with no
-- annotation: `holds.read` is the equation on the `Ingredient`s, not one on
-- the `Text` inside them (docs/proposals/bool-as-proposition.md §5.4).
import Std (Bool, Eq, Text)

type Ingredient = { name: Text }

theorem sameIngredient (xs: List Ingredient) (target: Ingredient)
    (found: xs.any (candidate => candidate == target) = True): ∃ (x: Ingredient) => x = target :=
  let Witness x (Both _ holds) := found
  Witness x holds.read

theorem sameIngredientMatch (xs: List Ingredient) (target: Ingredient)
    (found: xs.any (candidate => candidate == target) = True): ∃ (x: Ingredient) => x = target := match found with
      | Witness x (Both _ holds) => Witness x holds.read
