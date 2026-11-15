-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: a match on a
-- lambda's variable doesn't count as a step from the matched field either.
-- `apply` gives the lambda a longer list than `v`, so `r` is as long as `v`
-- plus one, and `f` runs for ever.
type W: Type = | MkW (xs: List Nat)

def apply (xs: List Nat) (k: List Nat → Nat): Nat := k [0, 0, ..xs]

def f: W → Nat
  | MkW v => apply v (match
    | [_, ..r] => f (MkW r)
    | [] => 0)
