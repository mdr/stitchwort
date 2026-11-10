-- expect-error: E-CASES-BUDGET
-- `grow 20 Leaf` is a small value, its two halves shared, but written out it
-- is a tree of 2 million nodes: `cases` gives up before splitting `b`, which
-- would write the goal out in full (SW-2606).
import Std (Bool)

type Tree = | Leaf | Node (left: Tree) (right: Tree)

def grow (n: Nat) (tree: Tree): Tree := match n with
  | 0 => tree
  | Succ m => grow m (Node tree tree)

def pick (b: Bool) (tree: Tree): Tree := match b with
  | True => tree
  | False => tree

theorem pickGrown (b: Bool): pick b (grow 20 Leaf) = grow 20 Leaf := cases
