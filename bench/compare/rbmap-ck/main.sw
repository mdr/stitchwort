-- Lean's rbmap_checkpoint benchmark (tests/compile_bench/rbmap_checkpoint.lean,
-- from the reference-counting paper "Counting Immutable Beans"): rbmap, but
-- every FREQ-th version of the tree is kept alive, so an insert into a kept
-- version must copy its path where rbmap's would reuse it in place. Inserts
-- the keys N-1 down to 0 into a persistent red-black tree, mapping each key to
-- whether it is a multiple of 10, keeps the tree after each key that is a
-- multiple of FREQ (and the final tree), then prints how many trees are kept
-- and how many keys of the final tree map to `True`. The tree is the
-- program's own, not std's `Map`.
--
-- The arguments are N and FREQ (defaults 2000000 and 10; Lean's benchmark
-- keeps every version, `-- 2000000 1`; `-- 1000 10` for a small run).
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

--| The final tree after inserting `key` down to 0 into `tree` (each key mapped
--| to whether it is a multiple of 10), and then, newest first, the trees kept
--| after each key that is a multiple of `frequency`; `kept` holds the trees
--| kept so far.
def mkMap (frequency: Nat): Nat → Tree → List Tree → List Tree
  | Zero, tree, kept => [tree, ..kept]
  | Succ key, tree, kept =>
    let next := tree.insert key (key % 10 == 0)
    mkMap frequency key next (if key % frequency == 0 then [next, ..kept] else kept)

--| How many of `trees` have at least one node.
def countNodes: List Tree → Nat → Nat
  | [Node _ _ _ _ _, ..rest], total => countNodes rest (total + 1)
  | [_, ..rest], total => countNodes rest total
  | [], total => total

def main(): {IO, Fail} () :=
  let (count, frequency) := match IO.args() with
    | [] => (2000000, 10)
    | [text, every] => (Fail.need text.toNat "expected a count", Fail.need every.toNat "expected a frequency")
    | _ => Fail.fail "expected no arguments, or a count and a frequency"
  let frequency := if frequency == 0 then 1 else frequency
  let kept := mkMap frequency count Leaf []
  match kept with
    | [] => Fail.fail "no trees"
    | [latest, ..older] =>
      let flagged := latest.fold 0 (_ value acc => if value then acc + 1 else acc)
      IO.print "${countNodes kept 0} ${flagged}"
