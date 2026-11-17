-- expect-error: E-PARTIAL-MIXED
-- `tree.size` and `box.tree.size` are linked, before types are known, to
-- every `size` here, so the partial `Box.size` and the total `Tree.size`
-- look like one cycle. The error says the cycle may be only that guess,
-- and how to name the function meant (SW-3738).
type Tree = | Node (children: List Tree)
type Box = { tree: Tree }

def Tree.size: Tree → Nat
  | Node children => 1 + sizes children

def sizes: List Tree → Nat
  | [] => 0
  | [tree, ..rest] => tree.size + sizes rest

def Box.size (box: Box): {Partial} Nat := box.tree.size + Box.size box
