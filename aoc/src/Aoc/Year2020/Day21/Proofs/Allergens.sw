--| What the program's lists are: `allergens` is the listed allergens, once
--| each, alphabetically; `ingredients` the ingredients some food has; and
--| `couldHold` says an ingredient is in every food listing the allergen.

namespace Aoc.Year2020.Day21.Proofs
import Aoc.Year2020.Day21 (..)
import Aoc.Year2020.Day21 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Ord, Ordering, Text, Void)

theorem memAllergens ∀ (list: FoodList) (allergen: Allergen): allergen ∈ list.allergens ↔ Spec.Listed list allergen :=
  let all := list.foods.flatMap .allergens
  let sorted := List.sortOnPerm all.unique .name
  {
    forward = member => (List.memFlatMap .allergens allergen list.foods).forward ((List.memUnique allergen all).forward (List.memPerm _ _ sorted allergen member)),
    backward = listed =>
      List.memPerm _ _ (List.permSym _ _ sorted) allergen ((List.memUnique allergen all).backward ((List.memFlatMap .allergens allergen list.foods).backward listed))
  }

theorem distinctAllergens ∀ (list: FoodList): list.allergens.Distinct :=
  List.distinctPerm list.allergens _ (List.sortOnPerm _ .name) (List.distinctUnique (list.foods.flatMap .allergens))

theorem alphabeticalAllergens ∀ (list: FoodList): Spec.Alphabetical list.allergens :=
  List.sortBySorted (first second => Ord.compare first.name second.name) (first second => Ord.leTotal first.name second.name)
    (list.foods.flatMap .allergens |> .unique)

theorem memIngredients ∀ (list: FoodList) (ingredient: Ingredient):
    ingredient ∈ list.ingredients ↔ (∃ (food: Food) => food ∈ list.foods ∧ ingredient ∈ food.ingredients) :=
  let all := list.foods.flatMap .ingredients
  {
    forward = member => (List.memFlatMap .ingredients ingredient list.foods).forward ((List.memUnique ingredient all).forward member),
    backward = found => (List.memUnique ingredient all).backward ((List.memFlatMap .ingredients ingredient list.foods).backward found)
  }

--| An ingredient in every food that lists the allergen.
def InEvery (list: FoodList) (ingredient: Ingredient) (allergen: Allergen): Prop :=
  ∀ (food: Food) => food ∈ list.foods → allergen ∈ food.allergens → ingredient ∈ food.ingredients

theorem couldHoldIff ∀ (list: FoodList) (ingredient: Ingredient) (allergen: Allergen): list.couldHold ingredient allergen = True ↔ InEvery list ingredient allergen :=
  {
    forward = could food member listed =>
      match could.read food member with
        | Inl unlisted => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym ((List.memContains food.allergens allergen).backward listed)) unlisted.read))
        | Inr passes => passes.read,
    backward = every =>
      List.allOfAll _ list.foods (List.allOfMem _ list.foods (food member =>
        match lists: food.allergens.contains allergen with
          | True => (List.memContains food.ingredients ingredient).backward (every food member lists.read)
          | False => rfl))
  }
