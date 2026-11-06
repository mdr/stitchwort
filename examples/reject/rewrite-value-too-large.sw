-- expect-error: E-RESOURCE
-- A `rewrite` whose right side computes to a huge value (`grow 30` written
-- out has 2^30 nodes) runs out of resources; the error points at the
-- `rewrite` and names the definition whose call was too large.
import Std (Eq, Nat)

type Tree =
  | Leaf (n: Nat)
  | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

theorem big (x: Nat) (t: Tree) (same: t = grow 30 (Leaf x)) (p: Tree → Prop) (h: p t): p (grow 30 (Leaf x)) :=
  rewrite same in h
