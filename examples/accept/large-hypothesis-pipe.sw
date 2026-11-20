-- A hypothesis whose type holds a call that computes to a huge value
-- (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2 million a value
-- read back may have), piped into a lambda: the annotation the kernel needs
-- on the lambda is the hypothesis's type with its calls as written, rather
-- than running out (SW-4336, as SW-4237 did for other read-backs).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

def pipeBig (x: Nat) (q: Tree → Prop) (big: q (grow 22 (Leaf x))): Nat := big |> (b => x)
