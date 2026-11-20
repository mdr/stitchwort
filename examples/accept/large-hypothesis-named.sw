-- A function used with a named argument and its other arguments left out,
-- whose parameter types hold a call that computes to a huge value (`grow 22
-- (Leaf x)` written out has 2^22 nodes, over the 2 million a value read back
-- may have): the lambda the missing arguments become is annotated with the
-- parameter types as written, rather than running out (SW-4333, as SW-4237
-- did for other read-backs).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

def size (x: Nat) (w: Wrap (grow 22 (Leaf x))) (k: Nat): Nat := match w with | MkWrap n => n + k

def withOne: (x: Nat) → Wrap (grow 22 (Leaf x)) → Nat := size (k := 1)
