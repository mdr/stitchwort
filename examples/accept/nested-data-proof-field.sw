-- A type nested in a container with a proof field still gets `==`, `<` and
-- `${…}`: the container's own derived instance compares its data and leaves
-- the proof out, as it does for a type's own proof field
-- (docs/proposals/derived-equality.md §5.4).

import Std (List, Nat, Text)

type Checked (a: Type) = { item: a, n: Nat, ok: n = n }

type T = | L | N (c: Checked T)

type Rose (a: Type) = | Leaf (x: a) | Node (c: Checked (List (Rose a)))

def one: T := N { item = L, n = 1, ok = byComputing }

def two: T := N { item = one, n = 1, ok = byComputing }

test "equal" := one == one
test "differs in the nested field" := one != two
test "differs in the data next to the proof" := one != N { item = L, n = 2, ok = byComputing }
test "order by constructor" := L < one && !(one < L)
test "order by field" := one < two && one < N { item = L, n = 2, ok = byComputing }
test "irreflexive" := !(one < one)
test "show" := "${one}" == "N { item = L, n = 1 }"

def rose: Rose Nat := Node { item = [Leaf 1], n = 1, ok = byComputing }

test "a parameterised group" := rose == rose && rose != Node { item = [Leaf 2], n = 1, ok = byComputing }
test "its order" := Leaf 1 < rose && !(rose < Leaf 1)
