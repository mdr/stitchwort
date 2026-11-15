-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: `MkText [c, ..cs]`
-- is the matched text rebuilt, not a smaller one, so `f` calls itself on
-- the same text for ever.
def f: Text → Nat
  | MkText [c, ..cs] => f (MkText [c, ..cs])
  | _ => 0
