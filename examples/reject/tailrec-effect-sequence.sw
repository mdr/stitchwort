-- expect-error: E-TAILREC
-- The call isn't the last statement of the block.
import Std (Nat)

ability Counter where
  bump: () → {Counter} ()

@[tailrec]
def f: Nat → {Counter} ()
  | 0 => ()
  | Succ n =>
    f n
    bump()
