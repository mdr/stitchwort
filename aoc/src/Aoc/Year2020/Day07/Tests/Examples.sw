--| Day 7's puzzle examples, a cycle, and the parser's errors.

namespace Aoc.Year2020.Day07.Tests
import Aoc.Year2020.Day07 (..)
import Std (Fail, List, Map, Nat, Result, Text)

def parsed (input: Text): Result Rules Text := Fail.toResult (() => parseRules input)

def part2 (input: Text): Result Nat Text := Fail.toResult (() => solvePart2 (parseRules input))

def example: Text := """
  light red bags contain 1 bright white bag, 2 muted yellow bags.
  dark orange bags contain 3 bright white bags, 4 muted yellow bags.
  bright white bags contain 1 shiny gold bag.
  muted yellow bags contain 2 shiny gold bags, 9 faded blue bags.
  shiny gold bags contain 1 dark olive bag, 2 vibrant plum bags.
  dark olive bags contain 3 faded blue bags, 4 dotted black bags.
  vibrant plum bags contain 5 faded blue bags, 6 dotted black bags.
  faded blue bags contain no other bags.
  dotted black bags contain no other bags.
  """

def example2: Text := """
  shiny gold bags contain 2 dark red bags.
  dark red bags contain 2 dark orange bags.
  dark orange bags contain 2 dark yellow bags.
  dark yellow bags contain 2 dark green bags.
  dark green bags contain 2 dark blue bags.
  dark blue bags contain 2 dark violet bags.
  dark violet bags contain no other bags.
  """

def lightRed: Colour := { shade = "light", hue = "red" }

test "example, the first rule" :=
  (parsed example).map (rules => rules.all.take 1)
    == Ok [
      {
        colour = lightRed,
        contents = [
          { count = 1, colour = { shade = "bright", hue = "white" } },
          { count = 2, colour = { shade = "muted", hue = "yellow" } }
        ]
      }
    ]
test "example, an empty rule" := (parsed example).map (rules => rules.all.drop 8 |> .map .contents) == Ok [[]]
test "example, the colours outside shiny gold" :=
  (parsed example).map (rules => (rules.outside shinyGold).toList.map .name)
    == Ok ["bright white", "dark orange", "light red", "muted yellow"]
test "example, part 1" := (parsed example).map solvePart1 == Ok 4
test "example, part 2" := part2 example == Ok 32
test "second example, part 1" := (parsed example2).map solvePart1 == Ok 0
test "second example, part 2" := part2 example2 == Ok 126

test "a bag with no rule holds nothing" := part2 "shiny gold bags contain 3 faded blue bags." == Ok 3
test "a cycle below shiny gold" :=
  part2
      "shiny gold bags contain 1 dark red bag.\ndark red bags contain 2 dark blue bags.\ndark blue bags contain 1 dark red bag."
    == Err "the rules for shiny gold bags go round in a cycle"
test "a cycle through shiny gold counts it for part 1" :=
  (parsed "shiny gold bags contain 1 dark red bag.\ndark red bags contain 2 shiny gold bags.").map solvePart1 == Ok 2
test "a cycle elsewhere is fine for part 2" :=
  part2
      "shiny gold bags contain 2 faded blue bags.\ndark red bags contain 1 dark blue bag.\ndark blue bags contain 1 dark red bag."
    == Ok 2

test "one bag must be singular" :=
  parsed "light red bags contain 1 bright white bags." == Err "line 1, column 42: expected ', ' or '.', got 's.'"
test "a capital letter" :=
  parsed "Light red bags contain no other bags." == Err "line 1, column 1: expected a colour, 'a' to 'z', got 'L'"
test "a missing full stop" :=
  parsed "light red bags contain no other bags" == Err "line 1, column 37: expected '.', got the end of the line"
