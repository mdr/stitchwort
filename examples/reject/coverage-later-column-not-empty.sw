-- expect-error: E-NONEXHAUSTIVE
-- Leaving out `Succ` is not excused: `Fin (Succ k)` has values (SW-181).

import Std (Fin)

def pick: (n: Nat) → (i: Fin n) → Nat
  | Zero, i => 0
