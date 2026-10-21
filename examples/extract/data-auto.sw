-- A type's `auto` parameter in generated JS (docs/proposals/interfaces.md
-- §7.5, §10): the ordering is a parameter of the tree's type, so it adds no
-- field to the tree; the operations take it as a dictionary argument.
--
-- run: sorted [3, 1, 2, 3]
-- run: sortedDown [3, 1, 2, 3]

interface Ordered (k: Type) =
  { compare: k -> k -> Ordering }

instance Ordered.instNat: Ordered Nat :=
  { compare = Nat.compare }

def descending: Ordered Nat := { compare = m n => Nat.compare n m }

type Tree (k: Type) [auto ord: Ordered k] =
  | Leaf
  | Node (left: Tree k) (key: k) (right: Tree k)

def Tree.insert [auto ord: Ordered k] (x: k): Tree k -> Tree k
  | Leaf       => Node Leaf x Leaf
  | Node l y r => match Ordered.compare x y with
    | Less    => Node (Tree.insert x l) y r
    | Equal   => Node l y r
    | Greater => Node l y (Tree.insert x r)

def Tree.toList: Tree k [ord := o] -> List k
  | Leaf       => []
  | Node l y r => List.append (Tree.toList l) (Cons y (Tree.toList r))

export def sorted (xs: List Nat): List Nat :=
  (xs.foldLeft (t x => Tree.insert x t) (Leaf: Tree Nat)).toList

export def sortedDown (xs: List Nat): List Nat :=
  (xs.foldLeft (t x => Tree.insert x t) (Leaf: Tree Nat [ord := descending])).toList
