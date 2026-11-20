-- A definition whose parameter's type holds a call that computes to a huge
-- value (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2 million
-- a value read back may have) is checked, its equations generated and its
-- uses elaborated with the call as written, rather than running out
-- (SW-4237, as SW-4091 did for `match`). Passing the parameter on to a
-- function whose type argument an unknown stands for solves that unknown
-- as the call too.
import Std (Eq, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

def keep [a: Type] (value: a): a := value

def size (x: Nat) (w: Wrap (grow 22 (Leaf x))): Nat := match w with | MkWrap n => n

def sizeKept (x: Nat) (w: Wrap (grow 22 (Leaf x))): Nat :=
  let kept := keep w
  size x kept
