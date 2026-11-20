-- A `Bool` test of equality is shown as it is written, inside `&&` as well
-- as alone: `xs == []` and `x != 4` (not `(x.decEq 4).not.holds`), in a
-- goal and in the equations `stitchwort doc` lists.
import Std (Bool, Nat, List)

def guarded (x: Nat) (xs: List Nat): Nat := if xs == [] && x != 4 then 0 else 1

theorem shown ∀ (x: Nat) (xs: List Nat)
    (h1: (xs == []) = True)
    (h2: (x != 4) = True)
    (h3: (xs == [] && x != 4) = True):
    guarded x xs = 0 :=
  ?
