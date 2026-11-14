--| Day 21 as the puzzle states it, about the foods' data (`Ingredient`,
--| `Allergen`, `Food`, `FoodList`): how the list is written, what a way of
--| the allergens being in the ingredients is, which ingredients can't
--| contain an allergen (part 1), and the canonical dangerous ingredient
--| list (part 2). Nothing else is shared with the program. The proofs
--| (Proofs/) show the program computes these.

namespace Aoc.Year2020.Day21.Spec
import Aoc.Year2020.Day21 (Allergen, Food, FoodList, Ingredient)
import Std (Char, List, NonEmptyList, Ordering, Parse, Text)

-- The format

--| An ingredient's name, in lower-case letters, and the space after it.
def IngredientWritten (read: List Char) (ingredient: Ingredient): Prop :=
  read = ingredient.name.toList ++ [' ']
    ∧ ingredient.name.toList ≠ []
    ∧ ingredient.name.toList.all Char.isAsciiLowercase = True

def AllergenWritten (read: List Char) (allergen: Allergen): Prop :=
  read = allergen.name.toList ∧ allergen.name.toList ≠ [] ∧ allergen.name.toList.all Char.isAsciiLowercase = True

def CommaWritten (read: List Char) (u: ()): Prop := read = ", ".toList

--| `mxmxvkd kfcds sqjhc nhms (contains dairy, fish)`: "each food's
--| ingredients list followed by some or all of the allergens the food
--| contains", the ingredients separated by spaces, the allergens by commas.
def FoodWritten (read: List Char) (food: Food): Prop :=
  ∃ (ingredientsRead: List Char) => ∃ (allergensRead: List Char) => read
    = ingredientsRead ++ "(contains ".toList ++ allergensRead ++ [')']
    ∧ (∃ (ingredients: NonEmptyList Ingredient) => Parse.Each IngredientWritten ingredientsRead ingredients.toList
      ∧ food.ingredients = ingredients.toList)
    ∧ (∃ (allergens: NonEmptyList Allergen) => Parse.SepBy AllergenWritten CommaWritten allergensRead allergens
      ∧ food.allergens = allergens.toList)

def LineBreakWritten (read: List Char) (u: ()): Prop := Parse.LineBreak read

--| One food a line.
def FoodListWritten (read: List Char) (list: FoodList): Prop :=
  ∃ (foods: NonEmptyList Food) => Parse.SepBy FoodWritten LineBreakWritten read foods ∧ list.foods = foods.toList

-- Where the allergens are

--| Some food lists the allergen.
def Listed (list: FoodList) (allergen: Allergen): Prop :=
  ∃ (food: Food) => food ∈ list.foods ∧ allergen ∈ food.allergens

--| A way the listed allergens could be in the ingredients: `holder`
--| names the ingredient each is in. "Each allergen is found in exactly one
--| ingredient. Each ingredient contains zero or one allergen", so no two
--| allergens are in the same one. "When they're listed ..., the ingredient
--| that contains each listed allergen will be somewhere in the
--| corresponding ingredients list."
def Holding (list: FoodList) (holder: Allergen → Ingredient): Prop :=
  (∀ (first second: Allergen) => Listed list first → Listed list second → holder first = holder second → first = second)
    ∧ (∀ (food: Food) => food ∈ list.foods
      → ∀ (allergen: Allergen) => allergen ∈ food.allergens → holder allergen ∈ food.ingredients)

--| The ingredient holds one of the allergens in some way they could be.
def CanContain (list: FoodList) (ingredient: Ingredient): Prop :=
  ∃ (holder: Allergen → Ingredient) => Holding list holder
    ∧ ∃ (allergen: Allergen) => Listed list allergen ∧ holder allergen = ingredient

-- Part 1

--| "Determine which ingredients can't possibly contain any of the
--| allergens in any food in your list. ... Counting the number of times
--| any of these ingredients appear in any ingredients list": the answer is
--| how many of the ingredients listed, food after food, can't contain one.
def Part1 (list: FoodList) (answer: Nat): Prop :=
  List.CountWith (ingredient => ¬CanContain list ingredient) (list.foods.flatMap .ingredients) answer

-- Part 2

--| No allergen's name after the next one's.
def Alphabetical (allergens: List Allergen): Prop :=
  List.Sorted (first second => Ordering.isLessEq (Text.compare first.name second.name)) allergens

--| "Arrange the ingredients alphabetically by their allergen and separate
--| them by commas to produce your canonical dangerous ingredient list":
--| `order` is the listed allergens, each once, alphabetically, and the
--| answer the names of the ingredients holding them, in that order.
def Part2 (list: FoodList) (answer: Text): Prop :=
  ∃ (holder: Allergen → Ingredient) => Holding list holder
    ∧ ∃ (order: List Allergen) => order.Distinct
      ∧ (∀ (allergen: Allergen) => allergen ∈ order ↔ Listed list allergen)
      ∧ Alphabetical order
      ∧ answer = (order.map holder |> .map .name |> .joinWith ",")
