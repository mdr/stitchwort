-- expect-error: E-LOCAL-DEFINITION
-- A local definition called `eq2` would be `total.eq2`, the name of
-- `total`'s second arm's generated equation (D2176).
import Std (List, Nat)

def total: List Nat → Nat
  | [] => 0
  | Cons x xs =>
    def eq2: Nat → Nat
      | n => n + x
    eq2 (total xs)
