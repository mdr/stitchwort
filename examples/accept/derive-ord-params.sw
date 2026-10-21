-- Derived `Ord` for types with parameters (docs/proposals/interfaces.md
-- §5.11): each type parameter the fields use asks for `[auto ord: Ord a]`
-- (`ordA`, `ordB`, … when there are several); value parameters are head
-- variables, as for `==`.

import Std (List, Nat, Ord)

type Tree (a: Type) = | Leaf | Node (left: Tree a) (value: a) (right: Tree a)

def leaf (x: a): Tree a := Node Leaf x Leaf

test "trees of numbers" := Ord.compare (leaf 1) (leaf 2) == Less
test "trees of text" := Ord.compare (leaf "b") (leaf "a") == Greater
test "leaf first" := Ord.compare Leaf (leaf 0) == Less
test "left subtree first" := Ord.compare (Node (leaf 9) 0 Leaf) (Node (leaf 1) 5 Leaf) == Greater

-- Two type parameters.
type Entry (k: Type) (v: Type) = { key: k, value: v }

def entries: List (Entry Text Nat) := [{ key = "b", value = 1 }, { key = "a", value = 2 }, { key = "a", value = 1 }]

test "two parameters" :=
  List.sort entries == [{ key = "a", value = 1 }, { key = "a", value = 2 }, { key = "b", value = 1 }]

-- A parameter used only by a proof field, and a value parameter.
type Bounded (limit: Nat) = | Within (n: Nat) (ok: Nat.leq n limit = True) | Over

test "value parameter" := Ord.compare (Within 2 rfl: Bounded 5) (Within 4 rfl) == Less

-- Derived instances nest: a tree of entries, sorted.
def forest: List (Tree (Entry Text Nat)) := [leaf { key = "z", value = 0 }, Leaf, leaf { key = "a", value = 0 }]

test "nested instances" :=
  List.sort forest == [Leaf, leaf { key = "a", value = 0 }, leaf { key = "z", value = 0 }]

-- A generic function given any derived ordering.
def smallest [auto ord: Ord a] (x: a) (y: a) (z: a): a := Ord.min x (Ord.min y z)

test "generic" := smallest (leaf 3) (leaf 1) (leaf 2) == leaf 1
