-- `match c: e` replaces `e` with the branch's constructor in the goal, in
-- every hypothesis that mentions it and in `let`-bound lemmas from before
-- the `match`; the equation `c` keeps `e` as written. So a refined
-- hypothesis is used as it is, and a refined lemma's premise is proved as
-- the branch states it.
import Std (Option, Void)

def isBig (n: Nat): Bool := 10 < n

def pick (n: Nat): Option Nat := if isBig n then None else Some n

-- `found` is `Some n = Some m` in the `False` branch: no rewrite needed.
theorem pickSmall (n: Nat) (m: Nat) (found: pick n = Some m): n = m :=
  match c: isBig n with
    | True => Void.exfalso (Option.noneNotSome m found)
    | False => Option.someInjective _ _ found

def needsSmall (n: Nat) (small: isBig n = False): Nat := n

-- `use`'s premise is `False = False` in the `False` branch.
def halveSmall (n: Nat): Nat :=
  let use := (small: isBig n = False) => needsSmall n small
  match c: isBig n with
    | True => 0
    | False => use rfl
