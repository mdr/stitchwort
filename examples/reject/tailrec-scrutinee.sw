-- expect-error: E-TAILREC
-- The call is what a `match` is on.
import Std (Nat)

@[tailrec]
def f: Nat → Nat
  | 0 => 0
  | Succ n =>
    match f n with
      | 0 => 1
      | _ => 2
