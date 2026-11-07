-- The Benchmarks Game's binary-trees: build and walk many short-lived
-- complete trees up to depth N (default 18; `-- 6` for a small run), with
-- one long-lived tree kept alive throughout. The game's output layout.
import Std (Fail, IO, List, Nat)

type Tree = | Leaf | Node (left: Tree) (right: Tree)

def Tree.make: Nat → Tree
  | Zero => Node Leaf Leaf
  | Succ depth => Node (Tree.make depth) (Tree.make depth)

def Tree.check: Tree → Nat
  | Leaf => 0
  | Node left right => 1 + left.check + right.check

--| The sum of the checks of `count` fresh trees of `depth`.
def checks: Nat → Nat → Nat → Nat
  | Zero, depth, total => total
  | Succ rest, depth, total => checks rest depth (total + (Tree.make depth).check)

def main(): {IO, Fail} () :=
  let maxDepth := match IO.args() with
    | [] => 18
    | [text] => Fail.need text.toNat "expected no arguments, or a depth"
    | _ => Fail.fail "expected no arguments, or a depth"
  let minDepth := 4
  let stretch := maxDepth + 1
  IO.print "stretch tree of depth ${stretch}\t check: ${(Tree.make stretch).check}"
  let longLived := Tree.make maxDepth
  List.foldLeft (List.range 0 ((maxDepth - minDepth) / 2 + 1)) () (u step =>
    let depth := minDepth + 2 * step
    let count := Nat.pow 2 (maxDepth - depth + minDepth)
    IO.print "${count}\t trees of depth ${depth}\t check: ${checks count depth 0}")
  IO.print "long lived tree of depth ${maxDepth}\t check: ${longLived.check}"
