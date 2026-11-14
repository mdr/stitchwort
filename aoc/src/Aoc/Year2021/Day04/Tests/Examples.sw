--| Day 4's tests: the example from the puzzle and unit tests.
-- Kept apart from the program, so `stitchwort run Aoc.Year2021.Day04.main`
-- doesn't check them.

namespace Aoc.Year2021.Day04.Tests
import Aoc.Year2021.Day04 (..)
import Aoc.Year2021.Day04.Spec (..)
import Std (Fail, List, Text)

def example: Text := """
  7,4,9,5,11,17,23,2,0,14,21,24,10,16,13,6,15,25,12,22,18,20,8,19,3,26,1

  22 13 17 11  0
   8  2 23  4 24
  21  9 14 16  7
   6 10  3 18  5
   1 12 20 15 19

   3 15  0  2 22
   9 18 13 17  5
  19  8  7 25 23
  20 11 10 24  4
  14 21 16 12  6

  14 21 17 24  4
  10 16 15  9 19
  18  8 23 26 20
  22 11 13  6  5
   2  0 12  3  7
  """

def exampleGame: Game := Fail.orElse { draws = [], boards = [] } (() => parseGame example)

def parsed (input: Text): Result Game Text := Fail.toResult (() => parseGame input)

test "parse the example" :=
  exampleGame.draws.length == 27
    ∧ exampleGame.boards.length == 3
    ∧ exampleGame.boards.map .rows |> .headOr []
      == [[22, 13, 17, 11, 0], [8, 2, 23, 4, 24], [21, 9, 14, 16, 7], [6, 10, 3, 18, 5], [1, 12, 20, 15, 19]]
test "example, part 1" := solvePart1 exampleGame == Some 4512
test "example, part 2" := solvePart2 exampleGame == Some 1924
--| The third board wins first, on the 12th draw (24); the second wins last,
--| on the 15th (13).
test "example, the turns" := exampleGame.boards.map (.winningTurn exampleGame.draws) == [13, 14, 11]
test "example, as the puzzle states it" :=
  (firstWinnerScore exampleGame, lastWinnerScore exampleGame) == (Some 4512, Some 1924)

test "a board too small" := parsed "1,2\n\n1 2\n3 4\n" == Err "board 1 isn't 5 by 5"
test "not a number" := parsed "1,x\n" == Err "line 1, column 3: expected a number, got 'x'"

--| Small games, 2 by 2. A column wins as a row does; a diagonal doesn't.
def tiny (draws: List Nat) (boards: List (List (List Nat))): Game := { draws, boards = boards.map (rows => { rows }) }
test "a column wins" := solvePart1 (tiny [1, 3, 9] [[[1, 2], [3, 4]]]) == Some 18
test "a diagonal doesn't" := solvePart1 (tiny [1, 4] [[[1, 2], [3, 4]]]) == None
--| Two boards win on the same draw: the earlier listed is first, the later
--| listed last.
test "the same draw" :=
  (
    solvePart1 (tiny [1, 2] [[[1, 2], [3, 4]], [[2, 1], [5, 6]]]),
    solvePart2 (tiny [1, 2] [[[1, 2], [3, 4]], [[2, 1], [5, 6]]])
  )
    == (Some 14, Some 22)
--| A board that never wins takes no part; draws after the last win change
--| nothing.
test "a board that never wins" := solvePart2 (tiny [1, 2, 3, 4] [[[1, 2], [5, 6]], [[7, 8], [9, 0]]]) == Some 22
test "no board wins" :=
  (solvePart1 (tiny [1] [[[1, 2], [3, 4]]]), solvePart2 (tiny [] [[[1, 2], [3, 4]]])) == (None, None)
--| A number drawn twice is marked once, and the score takes the draw that
--| completed the line.
test "a number drawn twice" := solvePart1 (tiny [1, 1, 2] [[[1, 2], [3, 4]]]) == Some 14
test "no boards" := (solvePart1 (tiny [1, 2] []), solvePart2 (tiny [1, 2] [])) == (None, None)

--| The examples, proved by computing them.
theorem examplePart1: solvePart1 exampleGame = Some 4512 := rfl
theorem examplePart2: solvePart2 exampleGame = Some 1924 := rfl

test "a board's lines and numbers" :=
  let board: Board := { rows = [[1, 2], [3, 4]] }
  board.lines == [[1, 2], [3, 4], [1, 3], [2, 4]] ∧ board.numbers == [1, 2, 3, 4]
