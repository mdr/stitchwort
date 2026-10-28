-- expect-error: E-AUTO-STUCK
-- `high - low ≠ 0` follows from `low < high` by `omega`, but this module
-- doesn't load `omega`'s library (nothing in it uses `omega`, `rewrite` or
-- `cases`), so `auto` doesn't try it. accept/auto-omega-facts.sw does.
import Std (Nat)

def remainderOfGap (n: Nat) (low: Nat) (high: Nat) (below: low < high): Nat := n % (high - low)
