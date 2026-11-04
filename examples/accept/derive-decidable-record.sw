-- A record of propositions whose fields can each be decided gets a derived
-- decision (SW-1015), as `And` has one: `byDecision`, `if h:` and the
-- counterexample search decide it.

import Std (List, Nat, byDecision)

type Small (n: Nat): Prop = { below: n < 10, notZero: n ≠ 0 }

theorem threeSmall: Small 3 := byDecision

def isSmall (n: Nat): Bool := if h: Small n then True else False

test "3 is small, 12 and 0 aren't" := isSmall 3 && !isSmall 12 && !isSmall 0

-- Each field is decided by what `if h:` finds: here `List.Distinct`'s and
-- `List.Mem`'s decisions.
type Roster (ids: List Nat) (captain: Nat): Prop = { distinct: List.Distinct ids, hasCaptain: captain ∈ ids }

theorem roster: Roster [1, 2, 3] 2 := byDecision

def valid (ids: List Nat) (captain: Nat): Bool := if h: Roster ids captain then True else False

test "a repeated id or a missing captain is no roster" := valid [1, 2] 1 && !valid [1, 1] 1 && !valid [1, 2] 3
