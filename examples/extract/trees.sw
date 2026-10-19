-- Recursive data types cross the boundary as nested tagged objects.
--
-- run: leaves (Node Leaf (Node Leaf Leaf))
-- run: mirror (Node Leaf (Node Leaf Leaf))

type Tree: Type =
  | Leaf
  | Node (left: Tree) (right: Tree)

export def leaves: Tree -> Nat
  | Leaf     => 1
  | Node l r => leaves l + leaves r

export def mirror: Tree -> Tree
  | Leaf     => Leaf
  | Node l r => Node (mirror r) (mirror l)
