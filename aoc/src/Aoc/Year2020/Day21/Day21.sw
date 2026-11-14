--| Advent of Code 2020, day 21: Allergen Assessment. Each line of the
--| input is a food: its ingredients, in a language you don't know, then
--| some of the allergens it contains, in English (`mxmxvkd kfcds sqjhc
--| nhms (contains dairy, fish)`). Each allergen is in exactly one
--| ingredient, and each ingredient has at most one allergen. Part 1 counts
--| how many times the ingredients that can't contain any allergen appear in
--| the foods. Part 2 lists the ingredients that do, in the alphabetical
--| order of their allergens, separated by commas.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day21.main < inputs/2020/day21.txt
--|
--| The ingredient holding an allergen is in every food that lists it, so
--| the ingredients that could hold it are those in all of those foods.
--| Part 2 settles which holds which with `Aoc.Common.assign`, as 2020 day
--| 16 does: an allergen with one candidate left takes it, and no other
--| allergen can then. The proofs are in `Aoc.Year2020.Day21.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day21.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day21
import Aoc.Common (assign)
import Std (Bool, Char, Fail, IO, List, NonEmptyList, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let list := parseFoods IO.readAll()
  IO.print "Part 1: ${list.safeAppearances}"
  match list.dangerousList with
    | Some dangerous => IO.print "Part 2: ${dangerous}"
    | None => Fail.fail "the foods don't settle which ingredient holds which allergen"

type Ingredient = { name: Text }

type Allergen = { name: Text }

--| A food's ingredients, and some of the allergens it contains (not
--| always all of them).
type Food = { ingredients: List Ingredient, allergens: List Allergen }

--| The foods, as the input lists them.
type FoodList = { foods: List Food }

-- The format

def word(): {Parse} Text := Parse.takeWhile1 "a word" Char.isAsciiLowercase

--| An ingredient, and the space after it.
def ingredient(): {Parse} Ingredient :=
  let name := word()
  Parse.char ' '
  { name }

def allergen(): {Parse} Allergen :=
  let name := word()
  { name }

def food(): {Parse} Food :=
  let ingredients := Parse.many1 ingredient
  Parse.text "(contains "
  let allergens := Parse.sepBy1 allergen (() => Parse.text ", ")
  Parse.char ')'
  { ingredients = ingredients.toList, allergens = allergens.toList }

def foodList(): {Parse} FoodList :=
  let foods := Parse.lines food
  { foods = foods.toList }

def parseFoods (input: Text): {Fail} FoodList := Parse.all input foodList

-- Part 1

--| Every allergen some food lists, once each, alphabetically.
def FoodList.allergens (list: FoodList): List Allergen := list.foods.flatMap .allergens |> .unique |> .sortOn .name

--| Whether `ingredient` is in every food that lists `allergen`: the
--| ingredient holding an allergen has to be.
def FoodList.couldHold (list: FoodList) (ingredient: Ingredient) (allergen: Allergen): Bool :=
  list.foods.all (food => not (food.allergens.contains allergen) || food.ingredients.contains ingredient)

def FoodList.isSafe (list: FoodList) (ingredient: Ingredient): Bool :=
  not (list.allergens.any (allergen => list.couldHold ingredient allergen))

--| Part 1: how many times the ingredients that can hold no allergen
--| appear, counting each food they're in.
def FoodList.safeAppearances (list: FoodList): Nat := list.foods.sumBy (food => food.ingredients.count list.isSafe)

-- Part 2

--| Every ingredient some food has, once each.
def FoodList.ingredients (list: FoodList): List Ingredient := list.foods.flatMap .ingredients |> .unique

def FoodList.candidates (list: FoodList) (allergen: Allergen): List Ingredient :=
  list.ingredients.filter (ingredient => list.couldHold ingredient allergen)

--| The ingredient holding each allergen, in the order of `allergens`, if
--| the elimination settles them all.
def FoodList.holders (list: FoodList): Option (List Ingredient) := assign (list.allergens.map list.candidates)

--| Part 2: the canonical dangerous ingredient list.
def FoodList.dangerousList (list: FoodList): Option Text :=
  list.holders.map (holders => holders.map .name |> .joinWith ",")
