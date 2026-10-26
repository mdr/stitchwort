-- expect-error: E-REFL
-- The goal mentions two opaque definitions: the error names both, and the
-- fix for each (`unfolding`, or rewriting with its `unfold` equation).
-- (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def double (n: Nat): Nat := n + n

opaque def triple (n: Nat): Nat := n + n + n

theorem both (n: Nat): double n + triple n = 5 * n := rfl
