-- expect-error: E-CALC-STEP
-- `|>` binds tighter than a step's relation, so the step is
-- `_ = (xs |> List.sum)`, and its proof must prove `3 = List.sum xs`.
import Std (List, Nat)

theorem sumIsThree (xs: List Nat) (h: List.sum xs = 3): 3 = (xs |> List.sum) :=
  calc 3
    _ = xs |> List.sum := h
