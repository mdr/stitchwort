import Std (List)

-- The fix `reject/match-dependent-scrutinee.sw`'s note suggests: a helper
-- takes both scrutinees as variables, which `match` generalises together.
type Tagged (n: Nat): Type = | MkTagged

def tag (xs: List Nat): Tagged (List.length xs) := MkTagged

def pred (n: Nat) (t: Tagged n): Nat := match n, t with
  | Zero, _ => 0
  | Succ k, _ => k

def good (xs: List Nat): Nat := 1 + pred (List.length xs) (tag xs)

def goodLocal (xs: List Nat): Nat :=
  def go (n: Nat) (t: Tagged n): Nat := match n, t with
    | Zero, _ => 0
    | Succ k, _ => k
  1 + go (List.length xs) (tag xs)
