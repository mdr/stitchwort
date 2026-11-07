inductive Tree where
  | leaf
  | node (left right : Tree)

-- `salt` differs between the two recursive calls only to stop Lean's common-subexpression
-- elimination from merging them into one shared subtree (as Lean's own binarytrees benchmark does).
def Tree.make (salt : Nat) : Nat → Tree
  | 0 => .node .leaf .leaf
  | depth + 1 => .node (Tree.make salt depth) (Tree.make (salt + 1) depth)

def Tree.check : Tree → Nat
  | .leaf => 0
  | .node left right => 1 + left.check + right.check

/-- The sum of the checks of `count` fresh trees of `depth`. -/
def checks : Nat → Nat → Nat → Nat
  | 0, _, total => total
  | count + 1, depth, total => checks count depth (total + (Tree.make 0 depth).check)

def main (args : List String) : IO Unit := do
  let maxDepth := match args with
    | [text] => text.toNat!
    | _ => 18
  let minDepth := 4
  let stretch := maxDepth + 1
  IO.println s!"stretch tree of depth {stretch}\t check: {(Tree.make 0 stretch).check}"
  let longLived := Tree.make 0 maxDepth
  for step in [0:(maxDepth - minDepth) / 2 + 1] do
    let depth := minDepth + 2 * step
    let count := 2 ^ (maxDepth - depth + minDepth)
    IO.println s!"{count}\t trees of depth {depth}\t check: {checks count depth 0}"
  IO.println s!"long lived tree of depth {maxDepth}\t check: {longLived.check}"
