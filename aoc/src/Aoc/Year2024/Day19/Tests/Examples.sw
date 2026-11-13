--| Day 19's tests: the example from the puzzle and unit tests.
--
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2024.Day19.main` doesn't check them.

namespace Aoc.Year2024.Day19.Tests
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (arrangements, possible, ways)
import Std (Fail, List, Nat, Result, Text)

def parsed (input: Text): Result Onsen Text := Fail.toResult (() => parseOnsen input)

--| Stripes from their letters, for writing tests.
def stripes (letters: Text): List Stripe :=
  letters.toList.map (match
    | 'w' => White
    | 'u' => Blue
    | 'b' => Black
    | 'r' => Red
    | _ => Green)

--| A pattern from its letters, which are never empty in these tests.
def patternOf (letters: Text): Pattern := match stripes letters with
  | [first, ..rest] => { stripes = [first, ..rest] }
  | [] => { stripes = [White] }

def designOf (letters: Text): Design := { stripes = stripes letters }

def onsenOf (patterns: List Text) (designs: List Text): Onsen := { patterns = patterns.map patternOf, designs = designs.map designOf }

def examplePatterns: List Pattern := ["r", "wr", "b", "g", "bwu", "rb", "gb", "br"].map patternOf

def example: Onsen := onsenOf ["r", "wr", "b", "g", "bwu", "rb", "gb", "br"] ["brwrr", "bggr", "gbbr", "rrbgbr", "ubwu", "bwurrg", "brgr", "bbrgwb"]

def exampleText: Text := """
  r, wr, b, g, bwu, rb, gb, br

  brwrr
  bggr
  gbbr
  rrbgbr
  ubwu
  bwurrg
  brgr
  bbrgwb
  """

def waysOf (design: Text): Nat := waysToMake examplePatterns (designOf design)

test "example, part 1" := solvePart1 example == 6
test "example, part 2" := solvePart2 example == 16

--| "Here are all of the different ways the above example's designs can be made".
test "example, the ways for each design" :=
  ["brwrr", "bggr", "gbbr", "rrbgbr", "ubwu", "bwurrg", "brgr", "bbrgwb"].map waysOf == [2, 1, 4, 6, 0, 1, 2, 0]

--| "brwrr can be made in two different ways: b, r, wr, r or br, wr, r."
test "example, the spec's ways to make brwrr" :=
  arrangements examplePatterns (designOf "brwrr") == [["b", "r", "wr", "r"].map patternOf, ["br", "wr", "r"].map patternOf]

test "example, the spec agrees on the short designs" :=
  ["bggr", "gbbr", "ubwu", "brgr"].all (design => ways examplePatterns (designOf design) == waysOf design)
test "example, the spec's impossible design" := !possible examplePatterns (designOf "ubwu") && possible examplePatterns (designOf "gbbr")

test "an empty design is made one way, with no towels" := waysToMake examplePatterns (designOf "") == 1 && ways examplePatterns (designOf "") == 1
test "no patterns make only the empty design" := waysToMake [] (designOf "r") == 0 && waysToMake [] (designOf "") == 1
test "a pattern equal to the design" := waysToMake [patternOf "bwu"] (designOf "bwu") == 1
test "a pattern longer than the design" := waysToMake [patternOf "bwur"] (designOf "bwu") == 0
test "overlapping patterns" := waysToMake (["r", "rr", "rrr"].map patternOf) (designOf "rrrr") == 7
test "overlapping patterns, the spec" := ways (["r", "rr", "rrr"].map patternOf) (designOf "rrrr") == 7
test "a pattern listed twice counts twice" := waysToMake (["g", "g"].map patternOf) (designOf "gg") == 4

--| A design of 100 red stripes from r and rr: the 101st Fibonacci number,
--| beyond 2^64.
test "counts beyond 64 bits" :=
  waysToMake (["r", "rr"].map patternOf) { stripes = List.replicate 100 Red } == 573147844013817084101

test "parse" := parsed exampleText == Ok example
test "parse without a final line break" := parsed "r, wr\n\nrwr" == Ok (onsenOf ["r", "wr"] ["rwr"])
test "a bad stripe" := parsed "r, x\n\nr\n" == Err "line 1, column 4: expected 'w', 'u', 'b', 'r' or 'g', got 'x'"
test "no blank line" := parsed "r, wr\nrwr\n" == Err "line 2, column 1: expected a blank line, got 'r'"
test "no designs" := parsed "r, wr\n\n" == Err "line 3, column 1: expected 'w', 'u', 'b', 'r' or 'g', got the end of the input"
