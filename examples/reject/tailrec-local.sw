-- expect-error: E-TAILREC
-- On a local definition too.
import Std (Nat)

def sumTo (n: Nat): Nat :=
  @[tailrec]
  def go: Nat → Nat
    | 0 => 0
    | Succ k => k + go k
  go n
