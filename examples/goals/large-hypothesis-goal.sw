-- An open goal whose context holds a hypothesis that computes to a huge
-- value (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2 million a
-- value read back may have) is shown with the call as written, rather than
-- writing the value out, which once took 24 GB with `grow 30` (SW-4091).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

theorem shown ∀ (x: Nat) (q: Tree → Prop) (big: q (grow 22 (Leaf x))): x + 0 = x := match x + 0 with | n => ?
