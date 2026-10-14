-- Recursive data types cross the boundary as nested tagged objects.
--
-- run: leaves (Node Leaf (Node Leaf Leaf))
-- run: mirror (Node Leaf (Node Leaf Leaf))

type Tree : Type =
  | Leaf
  | Node (left : Tree) (right : Tree)

export
leaves : Tree -> Nat
leaves Leaf       = 1
leaves (Node l r) = leaves l + leaves r

export
mirror : Tree -> Tree
mirror Leaf       = Leaf
mirror (Node l r) = Node (mirror r) (mirror l)
