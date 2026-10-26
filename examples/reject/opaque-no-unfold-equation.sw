-- expect-error: E-NO-UNFOLD-EQUATION
-- `start = 0` would compare a `Code` with a `Nat`, which is ill-typed where
-- `Code` is hidden, as it is in every type: so `start` has no `unfold`
-- equation. (docs/proposals/opaque-definitions.md §6.3.)
import Std (Nat)

opaque def Code: Type := Nat

opaque def start: Code unfolding Code := 0

theorem startItself: start = start := start.unfold
