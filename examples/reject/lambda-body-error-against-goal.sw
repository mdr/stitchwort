-- expect-error: E-OMEGA
-- A lambda argument checked against the goal the expected type gives is
-- blamed for its own error, not for one against an unknown goal.
import Std (Nat, Option, Eq)

def applyTo [a: Type] [b: Type] (continue: a -> b) (x: a): b := continue x

theorem moved (n: Nat): Some (n + 0 + 1) = Some (n + 2) :=
  applyTo (x =>
    rewrite Nat.addZero n in
    Eq.cong Some (omega)) n
