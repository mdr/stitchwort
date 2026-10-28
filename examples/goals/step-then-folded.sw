-- A call that steps at once is shown as that one step, and a call it
-- steps to stays folded: `if True then concatenate a b else 0` is
-- `concatenate a b`, not what `concatenate a b` computes to.
import Std (Nat)

def concatenate (left: Nat) (right: Nat): Nat :=
  Nat.fromDigits ((Nat.digits left).append (Nat.digits right))

theorem stepsAtOnce (a: Nat) (b: Nat): (if True then concatenate a b else 0) = concatenate a b := ?
