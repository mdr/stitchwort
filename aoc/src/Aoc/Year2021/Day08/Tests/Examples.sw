--| Day 8's tests: the examples from the puzzle and unit tests.
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2021.Day08.main` doesn't check them.

namespace Aoc.Year2021.Day08.Tests
import Aoc.Year2021.Day08 (..)
import Aoc.Year2021.Day08.Spec (..)
import Std (Fail, List, Option, Result, Text)

def example: Text := """
  be cfbegad cbdgef fgaecd cgeb fdcge agebfd fecdb fabcd edb | fdgacbe cefdb cefbgd gcbe
  edbfga begcd cbg gc gcadebf fbgde acbgfd abcde gfcbed gfec | fcgedb cgb dgebacf gc
  fgaebd cg bdaec gdafb agbcfd gdcbef bgcad gfac gcb cdgabef | cg cg fdcagb cbg
  fbegcd cbd adcefb dageb afcb bc aefdc ecdab fgdeca fcdbega | efabcd cedba gadfec cb
  aecbfdg fbg gf bafeg dbefa fcge gcbea fcaegb dgceab fcbdga | gecf egdcabf bgf bfgea
  fgeab ca afcebg bdacfeg cfaedg gcfdb baec bfadeg bafgc acf | gebdcfa ecba ca fadegcb
  dbcfg fgd bdegcaf fgec aegbdf ecdfab fbedc dacgb gdcebf gf | cefg dcbef fcge gbcadfe
  bdfegc cbegaf gecbf dfcage bdacg ed bedf ced adcbefg gebcd | ed bcgafe cdgba cbgef
  egadfb cdbfeg cegd fecab cgb gbdefca cg fgcdab egfdb bfceg | gbdfcae bgc cg cgb
  gcafb gcf dcaebfg ecagb gf abcdeg gaef cafbge fdbac fegbdc | fgae cfgab fg bagce
  """

def single: Text := "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ab | cdfeb fcadb cdfeb cdbaf"

def parsed (input: Text): Result (List Entry) Text := Fail.toResult (() => parseEntries input)

def entriesOf (input: Text): List Entry := Fail.orElse [] (() => parseEntries input)

def p (letters: Text): Pattern := Pattern.ofLetters letters

test "parse the single entry" :=
  parsed single
    == Ok [
      {
        patterns = ["acedgfb", "cdfbe", "gcdfa", "fbcad", "dab", "cefabd", "cdfgeb", "eafb", "cagedb", "ab"].map p,
        outputs = ["cdfeb", "fcadb", "cdfeb", "cdbaf"].map p
      }
    ]
test "the single entry reads 5353" := solvePart2 (entriesOf single) == 5353
test "the single entry's digits" :=
  (entriesOf single).headOr { patterns = [], outputs = [] }
    |> (entry => entry.patterns.map (decodeDigit entry.patterns))
    |> (== [8, 5, 2, 3, 7, 9, 6, 4, 0, 1])
test "the single entry's wiring, as the puzzle draws it" :=
  (entriesOf single).headOr { patterns = [], outputs = [] }
    |> .wiring
    |> (== { a = C, b = F, c = G, d = A, e = B, f = D, g = E })

test "parse the example" := (entriesOf example).length == 10
test "example, part 1" := solvePart1 (entriesOf example) == 26
test "example, part 2" := solvePart2 (entriesOf example) == 61229
test "example, each output value" :=
  (entriesOf example).map Entry.value == [8394, 9781, 1197, 9361, 4873, 8418, 4548, 1625, 8717, 4315]

test "the display's digit scores" := digitScores == [42, 17, 34, 39, 30, 37, 41, 25, 49, 45]
test "the display reads as itself" := display.map (decodeDigit display) == List.range 0 10
test "the spec's digits are the display's" :=
  List.range 0 10
    |> .all (digit =>
      segments.all (segment => (digitPattern digit).has segment == (digitSegments digit).contains segment))

--| The spec on the single entry: its wiring decodes it, and reads 5353.
def singleWiring: Segment → Segment := ({ a = C, b = F, c = G, d = A, e = B, f = D, g = E }: Wiring).at
test "the spec reads the single entry as 5353" :=
  (entriesOf single).map (decodedValue singleWiring) == [5353] ∧ (entriesOf single).map (easyDigits singleWiring) == [0]
test "the spec: each of the single entry's patterns shows its digit" :=
  (entriesOf single).headOr { patterns = [], outputs = [] }
    |> .patterns
    |> .map (shown singleWiring)
    |> (== [Some 8, Some 5, Some 2, Some 3, Some 7, Some 9, Some 6, Some 4, Some 0, Some 1])
test "the spec: the display as drawn shows its digits" := display.map (shown (s => s)) == (List.range 0 10).map Some

test "a letter past g" :=
  parsed "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ah | cdfeb fcadb cdfeb cdbaf"
    == Err "line 1, column 58: expected ' ', got 'h'"
test "nine patterns" :=
  Result.isOk (parsed "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb | cdfeb fcadb cdfeb cdbaf") == False
test "two patterns the same" :=
  parsed "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb cagedb | cdfeb fcadb cdfeb cdbaf"
    == Err "line 1: no wiring found that shows the ten digits"
test "an output that is no digit" :=
  parsed "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ab | cdfeb fcadb cdfeb ac"
    == Err "line 1: no wiring found that shows the ten digits"
test "letters in any order" := p "fca" == p "acf" ∧ (p "acf").size == 3
