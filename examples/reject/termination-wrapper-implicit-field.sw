-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: an implicit field
-- counts as a field, so `Two [rest := …] xs` has two and isn't smaller. As
-- in termination-wrapper-two-fields.sw, the other field grows on every call
-- and `f (Two [rest := Leaf] [1])` never finishes.
type T: Type = | Leaf | Two [rest: T] (xs: List Nat)

def f: T → Nat
  | Leaf => 0
  | Two [rest := rest] [] => f rest
  | Two [rest := rest] [x, ..xs] => f (Two [rest := Two [rest := Two [rest := rest] xs] [x]] xs)
