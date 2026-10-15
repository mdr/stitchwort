-- A field whose type depends on an earlier field, matched after the later
-- fields are bound: matching `tag` refines the types of `payload` and `rest`.

PayloadType : Bool -> Type
PayloadType True  = Nat
PayloadType False = Bool

type Tree : Type =
  | Leaf
  | Node (tag : Bool) (payload : PayloadType tag) (rest : PayloadType tag -> Tree)

-- How many nodes, following `rest` with the payload (plus one, for numbers).
depth : Tree -> Nat
depth Leaf                    = 0
depth (Node True  n rest)     = Succ (depth (rest (n + 1)))
depth (Node False b rest)     = Succ (depth (rest (not b)))

-- A number node whose `rest` takes a number, then a boolean node.
example : Tree
example = Node True 5 (\n -> Node False True (\b -> if b then Node False b (\c -> Leaf) else Leaf))

test "depth" = depth example == 2
