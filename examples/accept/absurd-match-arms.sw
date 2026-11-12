-- `()` with no `=>` makes a `match` alternative absurd, as it makes an
-- equation absurd: the matched part's type has no values once the
-- alternative's other patterns are known and the types compute (D3534).

import Std (Bool, Void)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

-- Several scrutinees: in the `Rock` and `Paper` alternatives, `h` is
-- `False = True`.
theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=
  match theirs, h with
    | Rock, ()
    | Paper, ()
    | Scissors, _ => rfl

-- The same as equations.
theorem rockBeatsOnlyScissorsArms: (theirs: Move) -> beats Rock theirs -> theirs = Scissors
  | Rock, ()
  | Paper, ()
  | Scissors, _ => rfl

-- One scrutinee, and a result that is data.
def fromImpossible (h: Rock = Paper): Nat :=
  match h with
    | ()

-- A clause lambda.
def noVoid: Void -> Nat := match
  | ()
