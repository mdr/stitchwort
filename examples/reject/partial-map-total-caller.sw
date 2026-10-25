-- expect-error: E-PARTIAL
-- `List.map` is partial when its callback is, so a caller whose type doesn't
-- say `Partial` is refused.
import Std (List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def stepsOfAll (numbers: List Nat): List Nat := List.map numbers collatzSteps
