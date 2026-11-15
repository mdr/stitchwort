-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: only a constructor
-- with exactly one field around a strict part is smaller. `Two xs t` with
-- `xs` the matched list's tail isn't, since its other field can be bigger
-- than anything matched: here it grows on every call, so `f (Two [1] Leaf)`
-- never finishes, and a rule that looked only at `xs` would accept it.
type T: Type = | Leaf | Two (xs: List Nat) (rest: T)

def f: T → Nat
  | Leaf => 0
  | Two [] rest => f rest
  | Two [x, ..xs] rest => f (Two xs (Two [x] (Two xs rest)))
