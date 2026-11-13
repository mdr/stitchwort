-- `b || False` and `b && True` are the same term, `if b then True else
-- False`. On its own it's shown as that `if`, since either operator would
-- read as a slip for the other; as the last operand of a chain it takes the
-- chain's operator, as `List.all` and `List.any` compute (SW-946). A
-- comparison beside a `Bool` `&&` in an equation is the `Bool` comparison
-- (SW-944). Each goal pastes back as the same goal.
import Std (List)

theorem orFalse ∀ (b: Bool): b = (b || False) := ?

theorem allTwo ∀ (b: Bool) (c: Bool): List.all [b, c] (x => x) = b := ?

theorem anyTwo ∀ (b: Bool) (c: Bool): List.any [b, c] (x => x) = b := ?

theorem besideBool ∀ (k: Nat) (b: Bool): (k < 3) = (k < 3 && b) := ?
