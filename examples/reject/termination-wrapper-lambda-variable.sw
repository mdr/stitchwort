-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: the part inside the
-- one-field constructor is reached through matched fields only, never a
-- lambda's variable. Here `apply` gives the lambda a list as long as the
-- one matched, so `f (MkW [1])` calls `f (MkW [0])` and so on for ever.
type W: Type = | MkW (xs: List Nat)

def apply (xs: List Nat) (k: List Nat → Nat): Nat := k [0, ..xs]

def f: W → Nat
  | MkW [x, ..v] => apply v (u => f (MkW u))
  | _ => 0
