--| Day 10's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2021.Day10.main` doesn't check them.

namespace Aoc.Year2021.Day10.Tests
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Aoc.Year2021.Day10.Proofs (completesOfUnclosed, firstIllegalOfScan, scanBalanced)
import Std (Fail, List, Option, Text)

def exampleText: Text := """
  [({(<(())[]>[[{[]{<()<>>
  [(()[<>])]({[<{<<[]>>(
  {([(<{}[<>[]}>{[]{[(<()>
  (((({<>}<{<{<>}{[]{[]{}
  [[<[([]))<([[{}[[()]]]
  [{[{({}]{}}([{[{{{}}([]
  {<[[]]>}<{[{[{[]{()[[[]
  [<(<(<(<{}))><([]([]()
  <{([([[(<>()){}]>(<<{{
  <{([{{}}[<[[[<>{}]]]>[]]
  """

def parsed (input: Text): Result (List (List Token)) Text := Fail.toResult (() => parseLines input)

def example: List (List Token) := Fail.orElse [] (() => parseLines exampleText)

--| One line's tokens, without the parser (for the theorems below).
def tokens (line: Text): List Token := line.toList.filterMap (char => allTokens.find (token => token.char == char))

test "parse the example" := example.length == 10 ∧ example.headOr [] == tokens "[({(<(())[]>[[{[]{<()<>>"
test "a stray character" :=
  parsed "()\n(x)\n" == Err "line 2, column 2: expected a bracket or the end of the line, got 'x'"
test "an empty line is no tokens" :=
  parsed "()\n\n[]\n" == Ok [[Opener Round, Closer Round], [], [Opener Square, Closer Square]]

test "the example's first illegal characters" :=
  example.map (scan []) |> .filterMap (match some | Corrupted illegal => illegal)
    == [Curly, Round, Square, Round, Angle]
test "example, part 1" := solvePart1 example == 26397

test "a completion" :=
  scan [] (tokens "[({(<(())[]>[[{[]{<()<>>") == Unclosed [Curly, Curly, Square, Square, Round, Curly, Round, Square]
test "its score" := completionScore [Curly, Curly, Square, Square, Round, Curly, Round, Square] == 288957
test "the example's completion scores" := example.filterMap autocompleteScore == [288957, 5566, 1480781, 995444, 294]
test "example, part 2" := solvePart2 example == 288957

test "a balanced line is neither" :=
  corruptionScore (tokens "([]{<>})") == 0 ∧ autocompleteScore (tokens "([]{<>})") == None
test "a closer with nothing open is illegal" := scan [] (tokens "())") == Corrupted Round
test "the middle" := middle [5, 1, 3] == 3 ∧ middle [2] == 2 ∧ middle [4, 1, 3, 2] == 3
test "spec and program score a completion alike" :=
  completionTotal 0 [Curly, Curly, Square, Square, Round, Curly, Round, Square] == 288957

--| The puzzle's examples, proved through the spec.
theorem exampleIllegalCurly: FirstIllegal (tokens "{([(<{}[<>[]}>{[]{[(<()>") (Closer Curly) :=
  firstIllegalOfScan (tokens "{([(<{}[<>[]}>{[]{[(<()>") Curly rfl
theorem exampleIllegalRound: FirstIllegal (tokens "[[<[([]))<([[{}[[()]]]") (Closer Round) :=
  firstIllegalOfScan (tokens "[[<[([]))<([[{}[[()]]]") Round rfl
theorem exampleBalanced: Balanced (tokens "[<>({}){}[([])<>]]") := scanBalanced (tokens "[<>({}){}[([])<>]]") rfl
theorem exampleCompletion: Completes (tokens "[({(<(())[]>[[{[]{<()<>>") [Curly, Curly, Square, Square, Round, Curly,
      Round, Square] :=
  completesOfUnclosed rfl
