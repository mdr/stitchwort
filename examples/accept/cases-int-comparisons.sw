-- `cases` on `Bool` tests that compare `Int`s: each `==` is one atom, true or
-- false, and `omega` reads it in each case. `cases` doesn't take the `Int`
-- apart into `OfNat` and `NegSucc` (the 64-case budget).
import Std (Bool)

--| Of `x - 1`, `x` and `x + 1`, `y` is one exactly when it is within 1 of `x`.
theorem window ∀ (x: Int) (y: Int):
    (if x + (-1) == y then 1 else 0) + (if x == y then 1 else 0) + (if x + 1 == y then 1 else 0) = Bool.toNat (x + (-1) <= y && y <= x + 1) :=
  cases

theorem differentOrSame ∀ (x: Int) (y: Int) (z: Int):
    (if x == y then 1 else 0) + (if y == z then 1 else 0) + (if x == z then 1 else 0) <= 3 :=
  cases
