-- A `match` that waits for an unknown in its scrutinee's type (`acc`'s type,
-- fixed by `g k`), where that type holds a call that computes to a huge
-- value (`grow 22 (Leaf acc)` written out has 2^22 nodes, over the 2 million
-- a value read back may have): when it resumes, the scrutinee's type is read
-- back with its calls as written, rather than running out (SW-4351, as
-- SW-4342 did for a `let`).
import Std (Nat)

type Tree (a: Type) = | Leaf (x: a) | Node (left: Tree a) (right: Tree a)

def grow [a: Type]: Nat → Tree a → Tree a
  | Zero, tree => tree
  | Succ n, tree => grow n (Node tree tree)

type Wrap (a: Type) (t: Tree a) = | MkWrap (n: Nat)

def make [a: Type] (x: a): Wrap a (grow 22 (Leaf x)) := MkWrap 0

def unwrap (k: Nat): Nat :=
  let g := acc => match make acc with | MkWrap n => n
  g k
