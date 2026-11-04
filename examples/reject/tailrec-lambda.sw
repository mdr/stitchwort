-- expect-error: E-TAILREC
-- The call is inside a function, which runs when `List.map` calls it.
import Std (List, Nat)

@[tailrec]
def f: Nat → Nat
  | 0 => 0
  | Succ n => List.length ([1, 2].map (y => f n))
