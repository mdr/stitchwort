-- expect-error: E-CALC-STEP
-- A callback in a step's line is shown as written: `r => r + 0`, not as the
-- computation it is made into.
import Std (List)

theorem sums (n: Nat): List.sumBy (List.range n) (r => r) = List.sumBy (List.range n) (r => r + 0) :=
  calc List.sumBy (List.range n) (r => r)
    _ = List.sumBy (List.range n) (r => r + 0) := (rfl: 0 = 0)
