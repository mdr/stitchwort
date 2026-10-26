-- expect-error: E-REFL
-- The statement is false, and the counterexample search finds that by
-- running `double`'s real code; the proof can't use that body, which the
-- note says. (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

theorem doubleIsSucc (n: Nat): double n = n + 1 := rfl
