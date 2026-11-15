-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: the review's R7.3
-- (docs/reviews/SW-3359-recursion-through-map-soundness.md). Each `u` here is
-- a real tail of `v`, so closed runs finish, but evidence through a lambda's
-- variable would let the kernel unfold `f (MkW n)` on an unknown `n` for
-- ever: the call is under no stuck match. Refused until a rule for lambdas
-- (recursion through `map`, stage 2) has its own argument.
type W: Type = | MkW (xs: List Nat)

def tails: List Nat → (List Nat → Nat) → Nat
  | [], k => 0
  | [_, ..rest], k => k rest + tails rest k

def f: W → Nat
  | MkW v => tails v (u => f (MkW u))
