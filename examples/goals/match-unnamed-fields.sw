-- An arm whose pattern names less than another arm's: `other` covers lists
-- the first arm splits further. The goal is about `other`, as written; the
-- parts the split made have no name in this arm, so where the goal computes
-- through them they are shown as `next✝` and `tail✝` (named after the other
-- arm's variable and the fields of `Cons`).
import Std (Bool, List, Nat)

def allTrue: List Bool → Bool
  | [] => True
  | [first] => first
  | [first, second, ..more] => first && allTrue [second, ..more]

theorem shown ∀ (rest: List Bool) (all: allTrue [True, ..rest] = True): allTrue rest = True := match rest with
  | [next] => ?
  | other => ?
