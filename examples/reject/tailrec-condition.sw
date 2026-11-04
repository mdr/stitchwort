-- expect-error: E-TAILREC
-- The call decides an `if`.
import Std (Nat)

@[tailrec]
def f: Nat → Nat
  | 0 => 0
  | Succ n => if f n == 0 then 1 else 2
