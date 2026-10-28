-- Day 19's tests: the example from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day19.main` doesn't
-- check them.

namespace Aoc.Year2024.Day19.Tests
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (arrangements, possible, ways)
import Std (Fail, List, Nat, Result, Text)

def parsed (input: Text): Result Onsen Text := Fail.toResult (() => parseOnsen input)

-- Stripes from their letters, for writing tests.
def stripes (letters: Text): List Stripe :=
  letters.toList.map (letter =>
    match letter with
      | 'w' => White
      | 'u' => Blue
      | 'b' => Black
      | 'r' => Red
      | _ => Green)

def onsenOf (patterns: List Text) (designs: List Text): Onsen := { patterns = patterns.map stripes, designs = designs.map stripes }

def examplePatterns: List Pattern := ["r", "wr", "b", "g", "bwu", "rb", "gb", "br"].map stripes

def example: Onsen := onsenOf ["r", "wr", "b", "g", "bwu", "rb", "gb", "br"] ["brwrr", "bggr", "gbbr", "rrbgbr", "ubwu", "bwurrg", "brgr", "bbrgwb"]

def exampleText: Text := "r, wr, b, g, bwu, rb, gb, br\n\nbrwrr\nbggr\ngbbr\nrrbgbr\nubwu\nbwurrg\nbrgr\nbbrgwb\n"

def waysOf (design: Text): Nat := waysToMake examplePatterns (stripes design)

test "example, part 1" := solvePart1 example == 6
test "example, part 2" := solvePart2 example == 16

-- "Here are all of the different ways the above example's designs can be made".
test "example, the ways for each design" :=
  ["brwrr", "bggr", "gbbr", "rrbgbr", "ubwu", "bwurrg", "brgr", "bbrgwb"].map waysOf == [2, 1, 4, 6, 0, 1, 2, 0]

-- "brwrr can be made in two different ways: b, r, wr, r or br, wr, r."
test "example, the spec's ways to make brwrr" :=
  arrangements examplePatterns (stripes "brwrr") == [["b", "r", "wr", "r"].map stripes, ["br", "wr", "r"].map stripes]

test "example, the spec agrees on the short designs" :=
  ["bggr", "gbbr", "ubwu", "brgr"].all (design => ways examplePatterns (stripes design) == waysOf design)
test "example, the spec's impossible design" := !possible examplePatterns (stripes "ubwu") && possible examplePatterns (stripes "gbbr")

test "an empty design is made one way, with no towels" := waysToMake examplePatterns [] == 1 && ways examplePatterns [] == 1
test "no patterns make only the empty design" := waysToMake [] (stripes "r") == 0 && waysToMake [] [] == 1
test "a pattern equal to the design" := waysToMake [stripes "bwu"] (stripes "bwu") == 1
test "a pattern longer than the design" := waysToMake [stripes "bwur"] (stripes "bwu") == 0
test "overlapping patterns" := waysToMake (["r", "rr", "rrr"].map stripes) (stripes "rrrr") == 7
test "overlapping patterns, the spec" := ways (["r", "rr", "rrr"].map stripes) (stripes "rrrr") == 7
test "a pattern listed twice counts twice" := waysToMake (["g", "g"].map stripes) (stripes "gg") == 4

-- A design of 100 red stripes from r and rr: the 101st Fibonacci number,
-- beyond 2^64.
test "counts beyond 64 bits" :=
  waysToMake (["r", "rr"].map stripes) (List.replicate 100 Red) == 573147844013817084101

test "parse" := parsed exampleText == Ok example
test "parse without a final line break" := parsed "r, wr\n\nrwr" == Ok (onsenOf ["r", "wr"] ["rwr"])
test "a bad stripe" := parsed "r, x\n\nr\n" == Err "line 1, column 4: expected 'w' or 'u' or 'b' or 'r' or 'g', got 'x'"
test "no blank line" := parsed "r, wr\nrwr\n" == Err "line 2, column 1: expected a blank line, got 'r'"
test "no designs" := parsed "r, wr\n\n" == Err "line 3, column 1: expected 'w' or 'u' or 'b' or 'r' or 'g', got the end of the input"
