-- `==` on declared data types: when a type is declared, the compiler
-- derives a `DecEq` instance for it (`T.%instDecEq`, a name you can't
-- spell), which `==` and `auto` find. It works when every field can be
-- compared: enums, constructors with fields, recursive types, and
-- parameterised types (`Tree Nat` uses `Nat`'s instance for `a`), and proof
-- fields that are equations (examples/accept/eqeq-proof-fields.sw).
-- Skipped, with `E-INSTANCE-NONE` and a note saying why: function fields,
-- other proof fields, type fields, types defined together, Prop types, and
-- fields that depend on earlier ones (see reject/eqeq-data-*.sw).

import Std (Bool)

type Dir = | North | East | South | West

test "enum" := North == North
test "enum, different" := !(North == West)

type Turn = | Left (n: Nat) | Right (n: Nat) | Stay

test "constructor with a field" := Left 3 == Left 3
test "field differs" := !(Left 3 == Left 4)
test "constructor differs" := !(Left 3 == Right 3)
test "with and without field" := !(Stay == Left 0)
test "no field" := Stay == Stay

type Path =
  | Here
  | Step (d: Dir) (rest: Path)

test "recursive" := Step North (Step East Here) == Step North (Step East Here)
test "recursive, deep difference" := !(Step North (Step East Here) == Step North (Step West Here))
test "recursive, different length" := !(Step North Here == Step North (Step North Here))

type Tree (a: Type): Type =
  | Leaf
  | Node (l: Tree a) (x: a) (r: Tree a)

test "Tree Nat" := Node Leaf 1 (Node Leaf 2 Leaf) == Node Leaf 1 (Node Leaf 2 Leaf)
test "Tree Nat, different" := !(Node Leaf 1 Leaf == Node Leaf 2 Leaf)
test "Tree Nat, shape" := !(Node Leaf 1 Leaf == Node (Node Leaf 1 Leaf) 1 Leaf)
test "Tree Dir" := Node Leaf North (Node Leaf South Leaf) == Node Leaf North (Node Leaf South Leaf)
test "Tree Dir, different" := !(Node Leaf North Leaf == Node Leaf East Leaf)

type Either2 (a: Type) (b: Type): Type =
  | InL (x: a)
  | InR (y: b)

test "two parameters" := InL 1 == (InL 1: Either2 Nat Text)
test "two parameters, other side" := InR "a" == (InR "a": Either2 Nat Text)
test "two parameters, differs" := !(InR "a" == (InR "b": Either2 Nat Text))
test "two parameters, side differs" := !(InL 1 == (InR "a": Either2 Nat Text))

test "list of enums" := [North, East] == [North, East]
test "list of enums, different" := !([North, East] == [North, South])
test "Option of constructor" := Some (Left 2) == Some (Left 2)
test "Option of constructor, different" := !(Some (Left 2) == Some (Right 2))
test "Option, None" := !(Some Stay == None)
test "tuple" := (North, Right 1) == (North, Right 1)
test "tuple, different" := !((North, Right 1) == (North, Right 2))
test "list of trees" := [Node Leaf 1 Leaf, Leaf] == [Node Leaf 1 Leaf, Leaf]
test "list of trees, different" := !([Node Leaf 1 Leaf, Leaf] == [Leaf, Leaf])

-- A record containing user types gets `==` too.
type Move = { dir: Dir, steps: Nat, path: Path }

def mv (n: Nat): Move := { dir = North, steps = n, path = Step East Here }

test "record" := mv 2 == mv 2
test "record, different" := !(mv 2 == mv 3)

-- In a definition, too, not just at compile time.
def sameTree (t: Tree Dir) (u: Tree Dir): Bool := t == u

test "at run time" := sameTree (Node Leaf East Leaf) (Node Leaf East Leaf)
test "at run time, different" := !(sameTree (Node Leaf East Leaf) (Node Leaf West Leaf))

-- The derived decider is a proof: `auto` runs it at compile time, so this
-- only compiles if it says `Yes`.
def needsEq (x: Tree Nat) (y: Tree Nat): [auto h: x = y] -> Nat := 1

test "auto proof" := needsEq (Node Leaf 1 Leaf) (Node Leaf 1 Leaf) == 1

-- And a branch can use the equation it learns.
def pick (t: Tree Nat) (u: Tree Nat): Nat :=
  if h: t = u then
    needsEq t u
  else
    0

test "if h, equal" := pick Leaf Leaf == 1
test "if h, different" := pick Leaf (Node Leaf 1 Leaf) == 0
