-- expect-error: E-REFL
-- SW-2910: `play m m` unfolds to an `if` on `beats m m`, which waits for
-- `m`; the note says so instead of leaving the unfolded `if` to read.
import Std (Eq)

type Move = | Rock | Paper | Scissors

def beats: (mine: Move) → (theirs: Move) → Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

def play (mine: Move) (theirs: Move): Nat :=
  if beats mine theirs then 1
  else if beats theirs mine then 2
  else 0

theorem selfPlayDraws (m: Move): play m m = 0 := rfl
