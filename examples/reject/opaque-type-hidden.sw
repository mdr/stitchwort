-- expect-error: E-TYPE-MISMATCH
-- Types are checked with every opaque definition hidden, even in a
-- declaration whose body unfolds them: in this statement `start` is a
-- `Code`, not a `Nat`. (docs/proposals/opaque-definitions.md §6.4, rule 2.)
import Std (Nat)

opaque def Code: Type := Nat

opaque def start: Code unfolding Code := 0

theorem startZero: start = 0 unfolding start := rfl
