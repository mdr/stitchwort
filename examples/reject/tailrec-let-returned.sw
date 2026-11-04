-- expect-error: E-TAILREC
-- Binding the result and returning it is not the call itself in tail
-- position: write the call as the result.
import Std (List, Nat)

@[tailrec]
def count: List Nat → Nat
  | [] => 0
  | [_, ..xs] =>
    let r := count xs
    r
