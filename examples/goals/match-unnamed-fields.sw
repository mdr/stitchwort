-- An arm whose pattern names less than another arm's: `other` covers lists
-- the first arm splits further, so its goal mentions their parts. Those
-- parts have no name in this arm, so they're shown as `next✝`, `head✝` and
-- `tail✝` (named after the other arm's variable and the fields of `Cons`),
-- in the goal and in the hypotheses' types alike.
import Std (Bool, List, Nat)

def allTrue: List Bool → Bool
  | Nil => True
  | Cons first Nil => first
  | Cons first (Cons second more) => first && allTrue (Cons second more)

theorem shown (rest: List Bool) (all: allTrue (Cons True rest) = True): allTrue rest = True :=
  match rest with
    | Cons next Nil => ?
    | other => ?
