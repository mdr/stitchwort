-- A `let` annotated with a type holding a call that computes to a huge value
-- (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2 million a value
-- read back may have), then a `match` on it: the scrutinee's type is read
-- back with its calls as written, rather than running out (SW-4342, as
-- SW-4339 did for `calc`).
import Std (Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

def make (x: Nat): Wrap (grow 22 (Leaf x)) := MkWrap x

def unwrap (x: Nat): Nat :=
  let w: Wrap (grow 22 (Leaf x)) := make x
  match w with | MkWrap n => n
