-- expect-error: E-RESOURCE
-- `rewrite same in h` turns `h` into `p (grow 30 (Leaf x))`, which doesn't
-- match the goal `p (grow 13 (Leaf x))`, so the unifier tries to solve an
-- unknown with the value `grow 30 (Leaf x)`. That value shares its subtrees,
-- but a solution is written out as a tree of 2^30 nodes: the solution, like
-- a value read back, may only be so large (SW-2409).
import Std (Eq, Nat)

type Tree =
  | Leaf (n: Nat)
  | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

theorem big (x: Nat) (t: Tree) (same: t = grow 30 (Leaf x)) (p: Tree → Prop) (h: p t): p (grow 13 (Leaf x)) :=
  rewrite same in h
