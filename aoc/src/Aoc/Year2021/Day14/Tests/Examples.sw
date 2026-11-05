--| Day 14's tests: the puzzle's example, through the spec and the
--| program, and the parser.
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2021.Day14.main` doesn't check them.

namespace Aoc.Year2021.Day14.Tests
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (afterSteps, answer, quantity, step)
import Std (Fail, List, Map, Nat, Result, Text)

def parsed (input: Text): Result Manual Text := Fail.toResult (() => parseManual input)

def manualOf (input: Text): Manual := Fail.orElse { template = [], rules = [] } (() => parseManual input)

def exampleInput: Text :=
  "NNCB\n\nCH -> B\nHH -> N\nCB -> H\nNH -> C\nHB -> C\nHC -> B\nHN -> C\nNN -> C\nBH -> H\nNC -> B\nNB -> B\nBN -> B\nBB -> N\nBC -> B\nCC -> N\nCN -> C\n"

def example: Manual := manualOf exampleInput

def pairOf (first: Char) (second: Char): ElementPair := { first, second }

--| The pair counts after `steps` steps of the example.
def exampleCounts (steps: Nat): PairCounts := Nat.iterate steps (stepCounts (ruleTable example.rules)) (countPairs example.template)

--| The hypothesis of the parser's theorems can hold.
-- (the audit's random texts never parse)
theorem smallParses: parsed "AB\n\nAB -> C\n" = Ok ({ template = ['A', 'B'], rules = [{ pair = { first = 'A', second = 'B' }, insert = 'C' }] }) := rfl

test "parse the example" :=
  example.template == ['N', 'N', 'C', 'B'] && example.rules.length == 16 && List.head example.rules == Some ({ pair = { first = 'C', second = 'H' }, insert = 'B' })

--| The puzzle's polymers after one and two steps, by the spec.
theorem exampleStep1: afterSteps 1 example = "NCNBCHB".toList := rfl

theorem exampleStep2: afterSteps 2 example = "NBCCNBBBCBHCB".toList := rfl

test "example, after 4 steps" := afterSteps 4 example == "NBBNBNBBCCNBCNCCNBBNBBNBBBNBBNBBCBHCBHHNHCBBCBHCB".toList

test "example, after 10 steps" :=
  let polymer := afterSteps 10 example
  polymer.length == 3073 && quantity polymer 'B' == 1749 && quantity polymer 'C' == 298 && quantity polymer 'H' == 161 && quantity polymer 'N' == 865

--| The program's counts give the same element counts.
test "example, element counts from the pair counts after 10 steps" :=
  elementCount 'N' (exampleCounts 10) 'N' == 865 && elementCount 'N' (exampleCounts 10) 'B' == 1749 && elementCount 'N' (exampleCounts 10) 'H' == 161

test "example, part 1, by the spec" := answer 10 example == 1588
test "example, part 1" := solvePart1 example == 1588
test "example, part 2" := solvePart2 example == 2188189693529

test "the pairs after one step" :=
  Map.toList (exampleCounts 1) == [(pairOf 'B' 'C', 1), (pairOf 'C' 'H', 1), (pairOf 'C' 'N', 1), (pairOf 'H' 'B', 1), (pairOf 'N' 'B', 1), (pairOf 'N' 'C', 1)]

test "a pair without a rule stays" := solvePart1 (manualOf "AB\n\nCD -> E\n") == 0 && afterSteps 3 (manualOf "AB\n\nCD -> E\n") == ['A', 'B']

test "a one-element template" := parsed "A\n\nAA -> B\n" |> .map solvePart2 == Ok 0

test "two rules for one pair" := parsed "AB\n\nAB -> C\nCD -> E\nAB -> D\n" == Err "two rules for the pair AB"

test "a lowercase element" := parsed "AB\n\nAb -> C\n" == Err "line 3, column 2: expected a capital letter, got 'b'"

test "no blank line" := parsed "AB\nAB -> C\n" == Err "line 2, column 1: expected a blank line, got 'A'"
