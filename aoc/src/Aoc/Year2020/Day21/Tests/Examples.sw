--| Day 21's puzzle example (aoc/examples/2020/day21.txt): its foods, the
--| safe ingredients and part 1, the candidates and part 2.

namespace Aoc.Year2020.Day21.Tests
import Aoc.Year2020.Day21 (..)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result FoodList Text := Fail.toResult (() => parseFoods input)

def example: Text := include "../../../../../examples/2020/day21.txt"

def names (ingredients: List Ingredient): List Text := ingredients.map .name

test "the example has four foods" :=
  (parsed example).map (list => list.foods.map (food => (food.ingredients.length, food.allergens.length)))
    == Ok [(4, 2), (4, 1), (2, 1), (3, 1)]

test "the example's allergens, alphabetically" :=
  (parsed example).map (list => list.allergens.map .name) == Ok ["dairy", "fish", "soy"]

test "the example's safe ingredients" :=
  (parsed example).map (list => list.ingredients.filter list.isSafe |> names |> .sort)
    == Ok ["kfcds", "nhms", "sbzzf", "trh"]

test "the example, part 1" := (parsed example).map (.safeAppearances) == Ok 5

test "the example's candidates for fish" :=
  (parsed example).map (list => list.candidates { name = "fish" } |> names |> .sort) == Ok ["mxmxvkd", "sqjhc"]

test "the example, part 2" := (parsed example).map (.dangerousList) == Ok (Some "mxmxvkd,sqjhc,fvjkl")

test "a food lists its allergens" := not (parsed "abc def\n").isOk
