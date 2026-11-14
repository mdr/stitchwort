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

def exampleInput: Text := """
  NNCB

  CH -> B
  HH -> N
  CB -> H
  NH -> C
  HB -> C
  HC -> B
  HN -> C
  NN -> C
  BH -> H
  NC -> B
  NB -> B
  BN -> B
  BB -> N
  BC -> B
  CC -> N
  CN -> C
  """

def example: Manual := manualOf exampleInput

def pairOf (first second: Char): ElementPair := { first, second }

--| The pair counts after `steps` steps of the example.
def exampleCounts (steps: Nat): PairCounts :=
  Nat.iterate steps (stepCounts (ruleTable example.rules)) (countPairs example.template)

--| The hypothesis of the parser's theorems can hold.
-- (the audit's random texts never parse)
theorem smallParses: parsed """
  AB

  AB -> C
  """ = Ok { template = ['A', 'B'], rules = [{ pair = { first = 'A', second = 'B' }, insert = 'C' }] } := rfl

test "parse the example" :=
  example.template == ['N', 'N', 'C', 'B']
    && example.rules.length == 16
    && example.rules.head == Some { pair = { first = 'C', second = 'H' }, insert = 'B' }

--| The puzzle's polymers after one and two steps, by the spec.
theorem exampleStep1: afterSteps 1 example = "NCNBCHB".toList := rfl

theorem exampleStep2: afterSteps 2 example = "NBCCNBBBCBHCB".toList := rfl

test "example, after 4 steps" := afterSteps 4 example == "NBBNBNBBCCNBCNCCNBBNBBNBBBNBBNBBCBHCBHHNHCBBCBHCB".toList

test "example, after 10 steps" :=
  let polymer := afterSteps 10 example
  polymer.length == 3073
    && quantity polymer 'B' == 1749
    && quantity polymer 'C' == 298
    && quantity polymer 'H' == 161
    && quantity polymer 'N' == 865

--| The program's counts give the same element counts.
test "example, element counts from the pair counts after 10 steps" :=
  elementCount 'N' (exampleCounts 10) 'N' == 865
    && elementCount 'N' (exampleCounts 10) 'B' == 1749
    && elementCount 'N' (exampleCounts 10) 'H' == 161

test "example, part 1, by the spec" := answer 10 example == 1588
test "example, part 1" := solvePart1 example == 1588
test "example, part 2" := solvePart2 example == 2188189693529

test "the pairs after one step" :=
  Map.toList (exampleCounts 1)
    == [
      (pairOf 'B' 'C', 1),
      (pairOf 'C' 'H', 1),
      (pairOf 'C' 'N', 1),
      (pairOf 'H' 'B', 1),
      (pairOf 'N' 'B', 1),
      (pairOf 'N' 'C', 1)
    ]

test "a pair without a rule stays" := solvePart1 (manualOf """
  AB

  CD -> E
  """) == 0 && afterSteps 3 (manualOf """
  AB

  CD -> E
  """) == ['A', 'B']

test "a one-element template" := parsed """
  A

  AA -> B
  """ |> .map solvePart2 == Ok 0

test "two rules for one pair" := parsed """
  AB

  AB -> C
  CD -> E
  AB -> D
  """ == Err "two rules for the pair AB"

test "a lowercase element" := parsed "AB\n\nAb -> C\n" == Err "line 3, column 2: expected a capital letter, got 'b'"

test "no blank line" := parsed "AB\nAB -> C\n" == Err "line 2, column 1: expected a blank line, got 'A'"
