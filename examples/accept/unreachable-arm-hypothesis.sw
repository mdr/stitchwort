-- expect-warning: W-UNREACHABLE
-- An arm with a body whose case a hypothesis rules out warns: here `h` is
-- `False = True` for `Rock` and `Paper`, so those two arms can be deleted
-- (the editor shows them faded). The arm is still checked, and the proof is
-- the same as without them.

import Std (Bool, Void)

type Move = | Rock | Paper | Scissors

def beats: Move -> Move -> Bool
  | Rock, Scissors => True
  | Paper, Rock => True
  | Scissors, Paper => True
  | _, _ => False

theorem rockBeatsOnlyScissors (theirs: Move) (h: beats Rock theirs): theirs = Scissors := match theirs with
  | Rock => Void.exfalso (Bool.falseNotTrue h)
  | Paper => Void.exfalso (Bool.falseNotTrue h)
  | Scissors => rfl

-- An arm that binds the impossible value itself is how a proof uses it, not
-- a case ruled out beforehand: no warning.
theorem rockBeatsRock (p: beats Rock Rock): 1 = 2 := match p with
  | q => Void.exfalso (Bool.falseNotTrue q)

-- `()` already says the case can't happen: no warning.
theorem rockBeatsOnlyScissorsAbsurd (theirs: Move) (h: beats Rock theirs): theirs = Scissors := match theirs, h with
  | Rock, ()
  | Paper, ()
  | Scissors, _ => rfl
