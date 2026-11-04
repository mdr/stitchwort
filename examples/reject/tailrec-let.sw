-- expect-error: E-TAILREC
-- The result is bound, and the block goes on to use it.
import Std (List, Nat)

@[tailrec]
def count: List Nat → Nat
  | [] => 0
  | [_, ..xs] =>
    let r := count xs
    r + 1
