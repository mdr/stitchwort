-- expect-error: E-TYPE-MISMATCH
-- The pattern `(a, b)` is a pair, but the written type is `Nat`.

import Std (Nat)

def f: Nat → Nat := ((a, b): Nat) => a
