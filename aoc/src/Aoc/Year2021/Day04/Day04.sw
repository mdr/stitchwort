--| Advent of Code 2021, day 4: bingo against a giant squid. The input is the
--| numbers to be drawn, in order, on one line, then the bingo boards, each a
--| 5 by 5 grid of numbers, separated by blank lines. A drawn number is marked
--| on every board that has it, and a board wins when every number in one of
--| its rows or columns is marked. A board's score is the sum of its numbers
--| not marked, times the number just drawn. Part 1 is the score of the first
--| board to win, part 2 of the last.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day04.main < inputs/2021/day04.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program doesn't play the game draw by draw. It finds when each number
--| is drawn (its position among the draws); a row or column is complete on
--| the turn its last number is drawn, and a board wins on the turn its first
--| row or column is complete. The boards are then taken turn by turn. The
--| proofs that both answers are those of the game played draw by draw, for
--| every input, are in `Aoc.Year2021.Day04.Proofs` (Proofs/), and the tests
--| in `Aoc.Year2021.Day04.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day04
import Std (Fail, IO, List, Nat, Parse)
import Std.Parse (blankLine, char, lines, many1, nat, sections, sepBy1, token)

def main(): {IO, Fail} () :=
  let game := parseGame IO.readAll()
  IO.print "Part 1: ${solvePart1 game |> .orFail "no board wins"}"
  IO.print "Part 2: ${solvePart2 game |> .orFail "no board wins"}"

--| A bingo board: its rows of numbers.
type Board = { rows: List (List Nat) }

--| The numbers to draw, in order, and the boards.
type Game = { draws: List Nat, boards: List Board }

--| The draws on the first line, separated by commas; a blank line; then the
--| boards, separated by blank lines, each row on a line with its numbers
--| separated by spaces. A board that isn't 5 by 5 fails, naming it.
def parseGame (input: Text): {Fail} Game :=
  let game: Game := Parse.all input (() =>
    let draws := sepBy1 nat (() => char ',') |> .toList
    blankLine()
    let boards :=
      sections (() => lines (() => many1 (() => token nat) |> .toList) |> .toList) |> .toList |> .map (rows => { rows })
    { draws, boards })
  match game.boards.withIndex.find (((_, board)) => not board.isFiveByFive) with
    | Some (index, _) => Fail.fail "board ${index + 1} isn't 5 by 5"
    | None => game

def Board.isFiveByFive (board: Board): Bool := board.rows.length == 5 ∧ board.rows.all (.length == 5)

--| A board's rows and columns.
def Board.lines (board: Board): List (List Nat) := board.rows ++ board.rows.transpose

--| All the numbers on a board, row by row.
def Board.numbers (board: Board): List Nat := board.rows.concat

--| The turn a board wins on, counting the draws from 0. A number is drawn on
--| the turn of its first place among the draws; a row or column is complete
--| on the turn its last number is drawn, and the board wins on the turn its
--| first row or column is. A number never drawn counts as drawn on turn
--| `draws.length`, after the last (`indexOf` gives the length when it finds
--| nothing), and so does a board that never wins: no turn takes it.
def Board.winningTurn (board: Board) (draws: List Nat): Nat :=
  board.lines
    |> .map (line => line.foldLeft 0 (latest number => Nat.max latest (draws.indexOf number)))
    |> .foldLeft draws.length Nat.min

--| The score of a board that wins on `turn`: its numbers not drawn by then,
--| added up, times the number drawn on that turn.
def Board.score (board: Board) (draws: List Nat) (turn: Nat): Nat :=
  (board.numbers.filter (number => turn < draws.indexOf number) |> .sum) * draws.getOr turn 0

--| The scores of the boards that win, in the order they win: turn by turn,
--| and in the order they are listed when several win on the same turn.
def winningScores (game: Game): List Nat :=
  let turns := game.boards.map (board => (board.winningTurn game.draws, board))
  List.range 0 game.draws.length
    |> .flatMap (turn => turns.filter (((won, _)) => won == turn) |> .map (((_, board)) => board.score game.draws turn))

--| Part 1: the score of the first board to win; `None` if none does.
def solvePart1 (game: Game): Option Nat := (winningScores game).head

--| Part 2: the score of the last board to win; `None` if none does.
def solvePart2 (game: Game): Option Nat := (winningScores game).last
