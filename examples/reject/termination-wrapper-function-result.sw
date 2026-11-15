-- expect-error: E-TERMINATION
-- Pairs with accept/text-patterns-prefix-recursion.sw: another function's
-- result isn't a part, even written with a dot like a field. `t.grow` is
-- `[t, t]`, so `f (MkForest [t])` calls `f (MkForest [t, t])` for ever.
type Tree: Type = | Node (label: Nat) (kids: List Tree)
type Forest: Type = | MkForest (trees: List Tree)

def Tree.grow (t: Tree): List Tree := [t, t]

def f: Forest → Nat
  | MkForest [t, ..ts] => f (MkForest t.grow)
  | _ => 0
