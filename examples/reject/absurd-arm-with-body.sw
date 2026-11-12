-- expect-error: E-TYPE-MISMATCH
-- `()` with `=>` after it is the unit pattern, not the absurd one: `h` is
-- `False = True` here, not `()`, and the note says to leave out the `=>`.

import Std (Bool)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs, h with
    | Rock, () => rfl
    | Paper, ()
    | Scissors, _ => rfl
