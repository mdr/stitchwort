-- expect-error: E-TAILREC
-- Every call that isn't a tail call is labelled, in one error.
import Std (List, Nat)

@[tailrec]
def f: List Nat → Nat
  | [] => 0
  | [x, ..xs] => f xs + Nat.max x (f xs)
