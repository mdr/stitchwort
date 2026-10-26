-- expect-error: E-DECREASING
-- A definition with `decreasing` has its body checked as a generated
-- transparent definition, which can't unfold opaque ones (yet).
-- (docs/proposals/opaque-definitions.md §6.3.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

opaque def halve (n: Nat): Nat
    decreasing n
    unfolding double
:=
  if n < 2 then 0 else 1 + halve (n - 2) [decreasing := omega]
