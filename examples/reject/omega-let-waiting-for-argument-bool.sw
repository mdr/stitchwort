-- expect-error: E-OMEGA
-- A `let` that is a function ending in a Boolean fact about its parameter:
-- the note still says which argument it is waiting for. Reading that fact
-- reads its parts back with the parameter in scope (SW-1448).
import Std (Nat)

def above (n: Nat): Nat.leq (Succ n) n = False := omega

theorem notLess (x: Nat) (y: Nat) (h: x ≤ y): x < y :=
  let reached := above
  omega
