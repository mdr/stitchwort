-- expect-error: E-UNFOLDING-GROUP
-- Definitions that call each other are checked together, so none has a body
-- yet while the others are checked: one can't unfold another.
-- (docs/proposals/opaque-definitions.md §6.11.)
import Std (Nat)

opaque def isEven: Nat -> Bool
  | Zero => True
  | Succ n => isOdd n

opaque def isOdd: Nat -> Bool
    unfolding isEven
  | Zero => False
  | Succ n => isEven n
