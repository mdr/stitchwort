-- expect-error: E-MATCH-MOTIVE

import Std (List)

def two (m: Nat) (p: m = 2): Bool → Nat
  | True => m
  | False => 0

-- Generalising `length [1, 1]` (which is 2) makes `q`'s type ill-formed.
def bad (b: Bool) (q: two (List.length [1, 1]) rfl b = 2): Nat := match List.length [1, 1] with
  | Zero => 0
  | Succ k => k
