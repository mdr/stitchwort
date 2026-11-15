-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: a record field read
-- with a dot is a call of the record's accessor, which the termination
-- check doesn't look into (termination-wrapper-function-result.sw shows
-- why it can't take a function's word for it), so `t.kids` isn't a part.
-- It's honest here; `| MkForest [{ kids, .. }, ..ts] => f (MkForest kids)`
-- is accepted.
type Tree: Type = { label: Nat, kids: List Tree }
type Forest: Type = | MkForest (trees: List Tree)

def f: Forest → Nat
  | MkForest [t, ..ts] => f (MkForest t.kids)
  | _ => 0
