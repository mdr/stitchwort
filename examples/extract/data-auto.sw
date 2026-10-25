-- A type's `auto` parameter in generated JS (docs/proposals/interfaces.md
-- §7.5, §10): the ordering is a parameter of the tree's type, so it adds no
-- field to the tree; the operations take it as a dictionary argument.
--
-- run: sorted [3, 1, 2, 3]
-- run: sortedDown [3, 1, 2, 3]

import Std (List, Nat)

interface Ordered (k: Type) =
  { compare: k -> k -> Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

def descending: Ordered Nat := { compare = m n => Nat.compare n m }

type Tree (k: Type) [auto ord: Ordered k] =
  | Leaf
  | Node (left: Tree k) (key: k) (right: Tree k)

def Tree.insert [auto ord: Ordered k]: Tree k -> k -> Tree k
  | Leaf, x => Node Leaf x Leaf
  | Node l y r, x => match Ordered.compare x y with
    | Less => Node (Tree.insert l x) y r
    | Equal => Node l y r
    | Greater => Node l y (Tree.insert r x)

def Tree.toList: Tree k [ord := o] -> List k
  | Leaf => []
  | Node l y r => List.append (Tree.toList l) (Cons y (Tree.toList r))

export def sorted (xs: List Nat): List Nat :=
  (xs.foldLeft (Leaf: Tree Nat) (t x => Tree.insert t x)).toList

export def sortedDown (xs: List Nat): List Nat :=
  (xs.foldLeft (Leaf: Tree Nat [ord := descending]) (t x => Tree.insert t x)).toList
