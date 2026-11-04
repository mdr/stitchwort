-- expect-error: E-TAILREC
-- The result of the call is added to `x` after it returns, so every call
-- keeps a frame.
import Std (List, Nat)

@[tailrec]
def total: List Nat → Nat
  | [] => 0
  | [x, ..xs] => x + total xs
