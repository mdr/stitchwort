--| Day 4 proved, for every input: both answers are those of the game played
--| draw by draw (Spec/).

namespace Aoc.Year2021.Day04.Proofs
import Aoc.Year2021.Day04 (..)
import Aoc.Year2021.Day04.Spec (..)
import Std (Decidable, Eq, List, Nat)

--| When a number is marked. The draws so far are `drawn`, and `rest` are
--| still to come. A number is marked once its first place among all the
--| draws is one of those drawn (`List.containsIndexOfAppend`).

--| Just after the draw of `number`, a number isn't marked when it is first
--| drawn later.
theorem unmarkedAfter ∀ (drawn: List Nat) (number: Nat) (later: List Nat) (x: Nat):
    not (marked (drawn ++ [number]) x) = (drawn.length < (drawn ++ [number, ..later]).indexOf x) :=
  rewrite List.containsIndexOfAppend x later (drawn ++ [number]),
      List.appendAssoc drawn [number] later,
      List.lengthSnoc drawn number in
    cases

--| A false `p` adds nothing to `p ∨ b`.
theorem orFalse ∀ (p b: Bool) (h: p = False): (p ∨ b) = b := rewrite h in rfl

--| So, once at least one number is drawn, a board has won exactly when the
--| program's winning turn has come.
theorem winsBefore ∀ (drawn rest: List Nat)
    (someDrawn: 0 < drawn.length) (board: Board):
    wins drawn board = (board.winningTurn (drawn ++ rest) < drawn.length) :=
  let drawnAt := (number: Nat) => List.indexOf (drawn ++ rest) number
  let lineTurn := (line: List Nat) => List.foldLeft line 0 (latest number => Nat.max latest (drawnAt number))
  let complete := (line: List Nat) =>
    calc List.all line (marked drawn)
      _ = List.all line (number => drawnAt number < List.length drawn) :=
        List.allCong line _ _ (number => List.containsIndexOfAppend number rest drawn)
      _ = (0 < List.length drawn ∧ List.all line (number => drawnAt number < List.length drawn)) := cases
      _ = (lineTurn line < List.length drawn) := Eq.sym (List.foldMaxLt drawnAt (List.length drawn) line 0)
  let notAfterAll: ((List.length (drawn ++ rest) < List.length drawn): Bool) = False :=
    omega [List.lengthAppend drawn rest]
  calc wins drawn board
    _ = List.any board.lines (line => List.all line (marked drawn)) :=
      Eq.sym (List.anyAppend board.rows (List.transpose board.rows) _)
    _ = List.any board.lines (line => lineTurn line < List.length drawn) := List.anyCong _ _ _ complete
    _ = List.any (List.map board.lines lineTurn) (turn => turn < List.length drawn) := Eq.sym (List.anyMap _ _ _)
    _ = (List.length (drawn ++ rest) < List.length drawn
        ∨ List.any (List.map board.lines lineTurn) (turn => turn < List.length drawn)) :=
      Eq.sym (orFalse _ _ notAfterAll)
    _ = (board.winningTurn (drawn ++ rest) < List.length drawn) :=
      Eq.sym
        (List.foldMinLt
          (turn => turn)
          (List.length drawn)
          (List.map board.lines lineTurn)
          (List.length (drawn ++ rest)))

--| The draw at `List.length drawn` is the one after `drawn`.
theorem drawOn ∀ (number: Nat) (later drawn: List Nat): (drawn ++ [number, ..later]).getOr drawn.length 0 = number :=
  match drawn with
    | [] => rfl
    | [first, ..others] => drawOn number later others

--| The spec's score of a board that wins on the draw of `number`, at
--| `List.length drawn`, is the program's.
theorem scoreAt ∀ (drawn: List Nat) (number: Nat) (later: List Nat) (board: Board):
    finalScore (drawn ++ [number]) number board = board.score (drawn ++ [number, ..later]) drawn.length :=
  rewrite List.filterCongMem (board.numbers) _ _ (x inBoard => unmarkedAfter drawn number later x),
      drawOn number later drawn in
    rfl

--| A board wins on the draw of `number` when its winning turn is no later.
theorem winsAfterDraw ∀ (drawn: List Nat) (number: Nat) (later: List Nat) (board: Board):
    wins (drawn ++ [number]) board = (board.winningTurn (drawn ++ [number, ..later]) < Succ drawn.length) :=
  rewrite winsBefore (drawn ++ [number]) later (omega [List.lengthSnoc drawn number]) board,
      List.appendAssoc drawn [number] later,
      List.lengthSnoc drawn number in
    rfl

--| Not won before turn `j` and won by its end is won on it.
theorem thisTurn ∀ (j t: Nat): ((j ≤ t < Succ j): Bool) = (t == j) := cases

--| Not won before turn `j` nor by its end is won later.
theorem laterTurn ∀ (j t: Nat): ((j ≤ t ∧ not (t < Succ j)): Bool) = (Succ j ≤ t) := cases

--| The game from any point: the boards that haven't won yet, playing the
--| draws to come, win turn by turn.
theorem playFrom ∀ (playing: List Board) (rest drawn: List Nat):
    play drawn (playing.filter (board => drawn.length ≤ board.winningTurn (drawn ++ rest))) rest
      = (List.rangeFrom rest.length drawn.length).flatMap (turn =>
        (playing.filter (board => board.winningTurn (drawn ++ rest) == turn)).map (board =>
          board.score (drawn ++ rest) turn)) :=
  match rest with
    | [] => rfl
    | [number, ..later] =>
      let turnOf := (board: Board) => board.winningTurn (drawn ++ [number, ..later])
      let wonNow :=
        Eq.trans
          (List.filterFilter (board => List.length drawn ≤ turnOf board) (wins (drawn ++ [number])) playing)
          (List.filterCongMem playing _ (board => turnOf board == List.length drawn) (board inPlaying =>
            rewrite winsAfterDraw drawn number later board in thisTurn (List.length drawn) (turnOf board)))
      let stillPlaying :=
        Eq.trans
          (List.filterFilter
            (board => List.length drawn ≤ turnOf board)
            (board => not (wins (drawn ++ [number]) board))
            playing)
          (List.filterCongMem playing _ (board => Succ (List.length drawn) ≤ turnOf board) (board inPlaying =>
            rewrite winsAfterDraw drawn number later board in laterTurn (List.length drawn) (turnOf board)))
      let afterNow: play
        (drawn ++ [number])
        (List.filter playing (board => Succ (List.length drawn) ≤ turnOf board))
        later
        = List.flatMap (List.rangeFrom (List.length later) (Succ (List.length drawn))) (turn =>
          List.map (List.filter playing (board => turnOf board == turn)) (board =>
            board.score (drawn ++ [number, ..later]) turn)) :=
        rewrite List.appendAssoc drawn [number] later, List.lengthSnoc drawn number at playFrom playing later
          (drawn ++ [number])
      rewrite wonNow, stillPlaying, afterNow, List.mapCong _ _ _ (scoreAt drawn number later) in rfl

--| The program's boards on a turn, found from their pairs with their turns.
theorem onTurn ∀ (draws: List Nat) (turn: Nat) (boards: List Board):
    ((boards.map (board => (board.winningTurn draws, board))).filter (((won, _)) => won == turn)).map (((_, board)) =>
      board.score draws turn)
      = (boards.filter (board => board.winningTurn draws == turn)).map (board => board.score draws turn) :=
  rewrite List.filterOfMap boards _ _, List.mapMap _ _ _ in rfl

--| The program's scores, in order, are the game's.
theorem winningScoresPlay ∀ (game: Game): winningScores game = play [] game.boards game.draws :=
  let everyBoard: List.filter game.boards (board => 0 ≤ board.winningTurn game.draws) = game.boards :=
    List.filterAll _ game.boards (board inBoards => rfl)
  calc winningScores game
    _ = List.flatMap (List.range 0 (List.length game.draws)) (turn =>
        List.map (List.filter game.boards (board => board.winningTurn game.draws == turn)) (board =>
          board.score game.draws turn)) := rewrite onTurn game.draws _ game.boards in rfl
    _ = play [] (List.filter game.boards (board => 0 ≤ board.winningTurn game.draws)) game.draws :=
      Eq.sym (playFrom game.boards game.draws [])
    _ = play [] game.boards game.draws := rewrite everyBoard in rfl

--| Part 1 is the puzzle's answer, for every input.
theorem part1Correct ∀ (game: Game): solvePart1 game = firstWinnerScore game :=
  Eq.cong List.head (winningScoresPlay game)

--| Part 2 is the puzzle's answer, for every input.
theorem part2Correct ∀ (game: Game): solvePart2 game = lastWinnerScore game :=
  Eq.cong List.last (winningScoresPlay game)
