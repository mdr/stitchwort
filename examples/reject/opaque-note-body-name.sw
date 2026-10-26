-- expect-error: E-REFL
-- Rewriting with `half.unfold` leaves the transparent copy of the body in
-- the goal. It reads "(body of half)" in the error, not `half.%body`.
-- (docs/proposals/opaque-definitions.md §6.3.)
import Std (Nat)

opaque def half (n: Nat): Nat := n / 2

theorem halfZero (n: Nat): half n = 0 :=
  rewrite half.unfold n in rfl
