-- expect-error: E-NONEXHAUSTIVE
-- A case left out that can happen is still an error, which names only
-- that case: with `h: beats Paper theirs`, `theirs` can be `Rock`, while
-- `Paper` and `Scissors` can't happen (D3534).

import Std (Bool, Nat)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

def score (theirs: Move) (h: beats Paper theirs): Nat :=
  match theirs with
    | Scissors => 0
