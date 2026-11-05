--| Day 4 as the puzzle states it: the numbers are drawn one at a time, each
--| is marked on every board, and after each draw the boards with a row or a
--| column all marked have won. The proofs (Proofs/) show the program computes
--| the same answers, for every input.
--|
--| What the puzzle leaves open is decided here:
--|
--| - Several boards winning on the same draw. They win in the order they
--|   are listed: the first board to win is the earliest listed of those
--|   that win first, and the last to win is the latest listed of those that
--|   win last.
--| - Boards that never win take no part: the last board to win is the last
--|   of those that do. If no board wins, neither part has an answer, and
--|   both are `None`.
--| - A board that has won stays won, so the draws after it don't change
--|   its score; the draws after every board has won change nothing.
--| - A number drawn twice is marked once; the score's "number that was just
--|   called" is the draw that completed the row or column.
--|
--| The boards are 5 by 5 in the puzzle (the parser checks it), but the spec
--| is defined for any board: its rows, and its columns as `List.transpose`
--| reads them (a row too short to reach a column is left out of it).

namespace Aoc.Year2021.Day04.Spec
import Aoc.Year2021.Day04 (Board, Game)
import Std (List)

--| Whether `number` is marked, once the numbers `drawn` have been drawn.
def marked (drawn: List Nat) (number: Nat): Bool := drawn.contains number

--| "If all numbers in any row or any column of a board are marked, that
--| board wins." Diagonals don't count.
def wins (drawn: List Nat) (board: Board): Bool :=
  board.rows.any (row => row.all (marked drawn)) ∨ board.rows.transpose.any (column => column.all (marked drawn))

--| "The sum of all unmarked numbers on that board", times "the number that
--| was just called when the board won".
def finalScore (drawn: List Nat) (justCalled: Nat) (board: Board): Nat :=
  (board.numbers.filter (number => not (marked drawn number)) |> .sum) * justCalled

--| The game, from the numbers `drawn` so far and the boards still `playing`:
--| draw the next number, then the boards that now win leave the game, in the
--| order they are listed, each with its score. The scores of the boards that
--| win, in the order they win.
def play (drawn: List Nat) (playing: List Board): (toDraw: List Nat) → List Nat
  | [] => []
  | [number, ..later] =>
    let drawnNow := drawn ++ [number]
    let won := playing.filter (wins drawnNow)
    let stillPlaying := playing.filter (board => not (wins drawnNow board))
    won.map (finalScore drawnNow number) ++ play drawnNow stillPlaying later

--| Part 1: "the score of the board that wins first".
def firstWinnerScore (game: Game): Option Nat := (play [] game.boards game.draws).head

--| Part 2: the score of "the board that will win last".
def lastWinnerScore (game: Game): Option Nat := (play [] game.boards game.draws).last
