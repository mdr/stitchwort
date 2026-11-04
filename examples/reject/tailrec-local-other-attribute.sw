-- expect-error: E-ATTRIBUTE
-- `noReceiver` doesn't apply to a local definition.
import Std (Nat)

def f (n: Nat): Nat :=
  @[noReceiver]
  def g: Nat → Nat
    | 0 => 0
    | Succ k => g k
  g n
