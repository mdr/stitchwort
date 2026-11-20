-- A handler whose computation's result type holds a call that computes to a
-- huge value (`grow 22 (Leaf x)` written out has 2^22 nodes, over the 2
-- million a value read back may have): the handler's translation writes the
-- result type into the terms it builds with the call as written, rather than
-- running out (SW-4333, as SW-4237 did for the effect checks).
import Std (Eq, Fail, Nat)

type Tree = | Leaf (n: Nat) | Node (left: Tree) (right: Tree)

def grow: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (t: Tree) = | MkWrap (n: Nat)

ability Log where
  say: Nat → {Log} Nat

def forward (x: Nat) (prog: () → {Log, Fail | e} Wrap (grow 22 (Leaf x))): {Fail | e} Wrap (grow 22 (Leaf x)) :=
  handle prog() with
    | return v => v
    | say n, k => k n

def forwardSome (x: Nat) (prog: () → {Log | e} Wrap (grow 22 (Leaf x))): {e} Option (Wrap (grow 22 (Leaf x))) :=
  handle prog() with
    | return v => Some v
    | say n, k => k n
