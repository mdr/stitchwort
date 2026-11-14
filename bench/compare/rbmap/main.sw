-- Lean's rbmap benchmark (tests/compile_bench/rbmap.lean, Leonardo de Moura
-- and Sebastian Ullrich's red-black tree from the reference-counting paper
-- "Counting Immutable Beans"): insert the keys N-1 down to 0 into a persistent
-- red-black tree, mapping each key to whether it is a multiple of 10, then
-- count the keys mapped to `True`. The tree is the program's own, not std's
-- `Map`. N is the argument (default 2000000, Lean's benchmark size; `-- 1000`
-- for a small run).
import Std (Bool, Fail, IO, List, Nat)

type Color = | Red | Black

--| A red-black tree from keys to flags. A node holds its colour, its two
--| subtrees and its key and value; every key in `left` is below `key` and
--| every key in `right` above it.
type Tree = | Leaf | Node (color: Color) (left: Tree) (key: Nat) (value: Bool) (right: Tree)

--| `step` applied to each key and value in key order, starting from `start`.
def Tree.fold: Tree → a → (Nat → Bool → a → a) → a
  | Leaf, acc, step => acc
  | Node _ left key value right, acc, step => right.fold (step key value (left.fold acc step)) step

--| Rebalances after an insertion into the left subtree: the argument is the new
--| left subtree of a black node holding `key`, `value` and `right`.
def balanceLeft: Tree → Nat → Bool → Tree → Tree
  | Node _ (Node Red l kx vx r1) ky vy r2, key, value, right =>
    Node Red (Node Black l kx vx r1) ky vy (Node Black r2 key value right)
  | Node _ l1 ky vy (Node Red l2 kx vx r), key, value, right =>
    Node Red (Node Black l1 ky vy l2) kx vx (Node Black r key value right)
  | Node _ l ky vy r, key, value, right => Node Black (Node Red l ky vy r) key value right
  | Leaf, key, value, right => Leaf

--| Rebalances after an insertion into the right subtree: the argument is the new
--| right subtree of a black node holding `left`, `key` and `value`.
def balanceRight: Tree → Nat → Bool → Tree → Tree
  | left, key, value, Node _ (Node Red l kx1 vx1 r1) ky vy r2 =>
    Node Red (Node Black left key value l) kx1 vx1 (Node Black r1 ky vy r2)
  | left, key, value, Node _ l1 ky vy (Node Red l2 kx2 vx2 r2) =>
    Node Red (Node Black left key value l1) ky vy (Node Black l2 kx2 vx2 r2)
  | left, key, value, Node _ l ky vy r => Node Black left key value (Node Red l ky vy r)
  | left, key, value, Leaf => Leaf

def Tree.isRed: Tree → Bool
  | Node Red _ _ _ _ => True
  | _ => False

--| Inserts without recolouring the root.
def Tree.ins: Tree → Nat → Bool → Tree
  | Leaf, key, value => Node Red Leaf key value Leaf
  | Node Red a ky vy b, key, value =>
    if key < ky then Node Red (a.ins key value) ky vy b
    else if key == ky then Node Red a key value b
    else Node Red a ky vy (b.ins key value)
  | Node Black a ky vy b, key, value =>
    if key < ky then if a.isRed then balanceLeft (a.ins key value) ky vy b else Node Black (a.ins key value) ky vy b
    else if key == ky then Node Black a key value b
    else if b.isRed then balanceRight a ky vy (b.ins key value)
    else Node Black a ky vy (b.ins key value)

def Tree.setBlack: Tree → Tree
  | Node _ l k v r => Node Black l k v r
  | e => e

def Tree.insert (tree: Tree) (key: Nat) (value: Bool): Tree :=
  if tree.isRed then (tree.ins key value).setBlack else tree.ins key value

--| The tree after inserting `count - 1` down to 0, each mapped to whether it
--| is a multiple of 10.
def mkMap: Nat → Tree → Tree
  | Zero, tree => tree
  | Succ key, tree => mkMap key (tree.insert key (key % 10 == 0))

def main(): {IO, Fail} () :=
  let count := match IO.args() with
    | [] => 2000000
    | [text] => Fail.need text.toNat "expected no arguments, or a count"
    | _ => Fail.fail "expected no arguments, or a count"
  let tree := mkMap count Leaf
  IO.print "${tree.fold 0 (_ value acc => if value then acc + 1 else acc)}"
