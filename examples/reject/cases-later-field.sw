-- expect-error: E-CASES
-- SW-975: `cases` takes `h` apart into `x = y` and `xs = ys`. The tail's
-- type `List a` is read under `Cons`'s parameter and earlier field; under
-- the parameter alone it was out of range and `cases` panicked. Now it adds
-- both facts, and says it can't close the false goal.
import Std (List, Nat)

theorem tailLength (x: Nat) (xs: List Nat) (y: Nat) (ys: List Nat) (h: Cons x xs = Cons y ys): xs.length = 5 :=
  cases
