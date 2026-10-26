-- expect-error: E-REFL
-- An opaque definition has no body while other declarations are checked,
-- so `rfl` can't see that `double 3` is `6` without `unfolding double`.
-- (docs/proposals/opaque-definitions.md §6.1.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

theorem doubleThree: double 3 = 6 := rfl
