-- expect-error: E-ATTRIBUTE
import Std (Nat)

@[tailrec "loop"]
def f: Nat → Nat
  | 0 => 0
  | Succ n => f n
