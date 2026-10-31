-- expect-error: E-UNSOLVED
-- The record literal's type is only worked out at the end of the
-- definition, from its field names, but the `match` after it needed the
-- type of what is found in `game.boards` sooner. The error is reported at
-- the literal, with a note to give its type there (`({ … }: Game)`) or on
-- the `let` (SW-946).

import Std (List)

type Game = { draws: List Nat, boards: List (List Nat) }

def made (make: () → a): a := make ()

def firstFull: Nat :=
  let game := made (() => { draws = [1], boards = [[1]] })
  match game.boards.withIndex.find (((_, board)) => board.length == 5) with
    | Some (index, _) => index
    | None => 0
