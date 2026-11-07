inductive Tree where
  | leaf
  | node (left right : Tree)

def Tree.make : Nat → Tree
  | 0 => .node .leaf .leaf
  | depth + 1 => .node (Tree.make depth) (Tree.make depth)

def Tree.check : Tree → Nat
  | .leaf => 0
  | .node left right => 1 + left.check + right.check

/-- The sum of the checks of `count` fresh trees of `depth`. -/
def checks : Nat → Nat → Nat → Nat
  | 0, _, total => total
  | count + 1, depth, total => checks count depth (total + (Tree.make depth).check)

def main (args : List String) : IO Unit := do
  let maxDepth := match args with
    | [text] => text.toNat!
    | _ => 18
  let minDepth := 4
  let stretch := maxDepth + 1
  IO.println s!"stretch tree of depth {stretch}\t check: {(Tree.make stretch).check}"
  let longLived := Tree.make maxDepth
  for step in [0:(maxDepth - minDepth) / 2 + 1] do
    let depth := minDepth + 2 * step
    let count := 2 ^ (maxDepth - depth + minDepth)
    IO.println s!"{count}\t trees of depth {depth}\t check: {checks count depth 0}"
  IO.println s!"long lived tree of depth {maxDepth}\t check: {longLived.check}"
