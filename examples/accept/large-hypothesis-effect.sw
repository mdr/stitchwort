-- A function with abilities whose result type holds a call that computes to
-- a huge value (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2
-- million a value read back may have): the check that the result's type
-- doesn't depend on the result of an operation reads the type with its
-- calls as written, rather than running out (SW-4237, as SW-4091 did for
-- `match`).
import Std (Eq, Fail, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

def make (x: Nat): {Fail} Wrap (grow 22 (Leaf x)) := MkWrap x

def makeAgain (x: Nat): {Fail} Wrap (grow 22 (Leaf x)) := make x
