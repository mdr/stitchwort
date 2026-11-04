-- expect-error: E-TAILREC
-- In a block of effects, a call whose result is bound and used by the
-- statements below isn't a tail call.
import Std (Nat)

ability Counter where
  bump: () → {Counter} ()

@[tailrec]
def f: Nat → {Counter} Nat
  | 0 => 0
  | Succ n =>
    bump()
    let r := f n
    r + 1
