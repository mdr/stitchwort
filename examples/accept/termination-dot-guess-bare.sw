-- A function passed without its argument (`shelf.boxes.map Box.size`) is
-- not a recursive call just because a dot call elsewhere might have meant
-- it. Before their types are known, `tree.size` and `box.tree.size` are
-- linked to every `size` here, so the four definitions are put in one group
-- to check; the kernel then gets the groups the checked bodies really make
-- (`Tree.size` with `sizes`, then each of the others on its own), so the
-- bare `Box.size` isn't an unsaturated call into its own group (SW-3738,
-- found in Toy++ as SW-3607 and SW-3671).
type Tree = | Node (children: List Tree)
type Box = { tree: Tree }
type Shelf = { boxes: List Box }

def Tree.size: Tree → Nat
  | Node children => 1 + sizes children

def sizes: List Tree → Nat
  | [] => 0
  | [tree, ..rest] => tree.size + sizes rest

def Box.size (box: Box): Nat := box.tree.size

def Shelf.size (shelf: Shelf): List Nat := shelf.boxes.map Box.size

-- A real cycle through a bare occurrence is still refused:
-- examples/soundness/higher-order-recursion.sw.
test "a shelf's sizes" := (Shelf.size { boxes = [{ tree = Node [Node []] }] }) == [2]
