-- expect-error: E-OMEGA
-- A `let` that leaves out its last argument is a function, not a fact;
-- the note says which argument it is still waiting for.
import Std (Nat)

def under (limit: Nat): 0 ≤ limit := Nat.leAddRight 0 limit

theorem notLess (x: Nat) (y: Nat) (h: x ≤ y): x < y :=
  let reached := under
  omega
