-- A container's proof field that is an equation over one of the group's
-- own type parameters: `W (Rose a) a` has `ok: v = v` over `a`, so the
-- derived `==`, `<` and `${…}` need `DecEq a` for it (and leave the proof
-- out), the dictionary being the one the group's parameter is given.

import Std (Nat, Text)

type W (b: Type) (c: Type) = { item: b, v: c, ok: v = v }

type Rose (a: Type) = | Leaf (x: a) | Node (w: W (Rose a) a)

def leaf (n: Nat): Rose Nat := Leaf n

def node (n v: Nat): Rose Nat := Node { item = leaf n, v = v, ok = rfl }

test "equal" := node 1 2 == node 1 2
test "differs in the nested item" := node 1 2 != node 3 2
test "differs in the data next to the proof" := node 1 2 != node 1 3
test "order by constructor" := leaf 5 < node 1 2 && !(node 1 2 < leaf 5)
test "order by item then value" := node 1 2 < node 1 3 && node 1 9 < node 2 0
test "show" := "${node 1 2}" == "Node { item = Leaf 1, v = 2 }"

-- The same through a group of two types.
type Tree (a: Type) = | Tip | Branch (w: W (Forest a) a)

type Forest (a: Type) = | Empty | Plant (t: Tree a) (rest: Forest a)

def branch (v: Nat): Tree Nat := Branch { item = Plant Tip Empty, v = v, ok = rfl }

test "a group: equal" := branch 1 == branch 1 && branch 1 != branch 2
test "a group: order" := Tip < branch 1 && branch 1 < branch 2
test "a group: show" := "${branch 1}" == "Branch { item = Plant Tip Empty, v = 1 }"
