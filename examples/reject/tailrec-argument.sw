-- expect-error: E-TAILREC
-- The call is an argument of `Nat.max`, which runs after it returns.
import Std (List, Nat)

@[tailrec]
def biggest: List Nat → Nat
  | [] => 0
  | [x, ..xs] => Nat.max x (biggest xs)
