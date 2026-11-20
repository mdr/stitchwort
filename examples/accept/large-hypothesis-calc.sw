-- A `calc` whose first expression has a type holding a call that computes to
-- a huge value (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2
-- million a value read back may have): the type the steps are checked at is
-- read back with its calls as written, rather than running out (SW-4339, as
-- SW-4237 did for equations).
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

def make (x: Nat): Wrap (grow 22 (Leaf x)) := MkWrap x

theorem viaCalc ∀ (x: Nat): make x = make x := calc make x
  _ = make x
