-- expect-error: E-AUTO-STUCK
-- `high - low ≠ 0` follows from `low < high` by `arithmetic`, but this module
-- doesn't load `arithmetic`'s library (nothing in it uses `arithmetic`, `rewrite` or
-- `cases`), so `auto` doesn't try it. accept/auto-omega-facts.sw does.
import Std (Nat)

def nonzero (d: Nat) [auto ok: d ≠ 0]: Nat := d

def gap (low: Nat) (high: Nat) (below: low < high): Nat := nonzero (high - low)
