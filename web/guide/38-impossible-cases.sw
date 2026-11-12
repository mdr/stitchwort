import Std (Bool, Void)

-- A case that can't happen needs no arm. Rock beats only scissors: when
-- `theirs` is `Rock` or `Paper`, `h` says `beats Rock theirs`, which
-- computes to `False = True`. Nothing proves that, so those cases can't
-- happen, and the compiler fills them in.
type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs with
    | Scissors => rfl

-- Try changing `beats Rock` to `beats Paper` above: then `theirs` can be
-- `Rock`, and the compiler asks for that arm.

-- To say so in the code, match on `h` too and write `()`, the pattern for
-- a value that can't exist, with no `=>`.
theorem rockBeatsOnlyScissorsAgain (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs, h with
    | Rock, ()
    | Paper, ()
    | Scissors, _ => rfl
