-- A field whose type depends on an earlier field, matched after the later
-- fields are bound: matching `tag` refines the types of `payload` and `rest`.

def PayloadType : Bool -> Type
  | True  => Nat
  | False => Bool

type Tree : Type =
  | Leaf
  | Node (tag : Bool) (payload : PayloadType tag) (rest : PayloadType tag -> Tree)

-- How many nodes, following `rest` with the payload (plus one, for numbers).
def depth : Tree -> Nat
  | Leaf              => 0
  | Node True  n rest => Succ (depth (rest (n + 1)))
  | Node False b rest => Succ (depth (rest (not b)))

-- A number node whose `rest` takes a number, then a boolean node.
def example : Tree := Node True 5 (\n => Node False True (\b => if b then Node False b (\c => Leaf) else Leaf))

test "depth" := depth example == 2
