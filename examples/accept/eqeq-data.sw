-- `==` on declared data types: when a type is declared, the compiler writes
-- a decision procedure for `=` on it (`T.%decEq`, a name you can't spell),
-- which `==` and `auto` find. It works when every field can be compared:
-- enums, constructors with fields, recursive types, and parameterised types
-- whose parameters are `Type` (`Tree Nat` uses `Nat`'s decider for `a`).
-- Skipped, with `E-AUTO-NONE` and a note saying why: function fields, proof
-- or type fields, types defined together, Prop types, and fields that
-- depend on earlier ones (see reject/eqeq-data-*.sw).

type Dir = | North | East | South | West

test "enum" := North == North
test "enum, different" := Bool.not (North == West)

type Turn = | Left (n : Nat) | Right (n : Nat) | Stay

test "constructor with a field" := Left 3 == Left 3
test "field differs" := Bool.not (Left 3 == Left 4)
test "constructor differs" := Bool.not (Left 3 == Right 3)
test "with and without field" := Bool.not (Stay == Left 0)
test "no field" := Stay == Stay

type Path =
  | Here
  | Step (d : Dir) (rest : Path)

test "recursive" := Step North (Step East Here) == Step North (Step East Here)
test "recursive, deep difference" := Bool.not (Step North (Step East Here) == Step North (Step West Here))
test "recursive, different length" := Bool.not (Step North Here == Step North (Step North Here))

type Tree (a : Type) : Type =
  | Leaf
  | Node (l : Tree a) (x : a) (r : Tree a)

test "Tree Nat" := Node Leaf 1 (Node Leaf 2 Leaf) == Node Leaf 1 (Node Leaf 2 Leaf)
test "Tree Nat, different" := Bool.not (Node Leaf 1 Leaf == Node Leaf 2 Leaf)
test "Tree Nat, shape" := Bool.not (Node Leaf 1 Leaf == Node (Node Leaf 1 Leaf) 1 Leaf)
test "Tree Dir" := Node Leaf North (Node Leaf South Leaf) == Node Leaf North (Node Leaf South Leaf)
test "Tree Dir, different" := Bool.not (Node Leaf North Leaf == Node Leaf East Leaf)

type Either2 (a : Type) (b : Type) : Type =
  | InL (x : a)
  | InR (y : b)

test "two parameters" := InL 1 == (InL 1 : Either2 Nat Text)
test "two parameters, other side" := InR "a" == (InR "a" : Either2 Nat Text)
test "two parameters, differs" := Bool.not (InR "a" == (InR "b" : Either2 Nat Text))
test "two parameters, side differs" := Bool.not (InL 1 == (InR "a" : Either2 Nat Text))

test "list of enums" := [North, East] == [North, East]
test "list of enums, different" := Bool.not ([North, East] == [North, South])
test "Maybe of constructor" := Just (Left 2) == Just (Left 2)
test "Maybe of constructor, different" := Bool.not (Just (Left 2) == Just (Right 2))
test "Maybe, Nothing" := Bool.not (Just Stay == Nothing)
test "tuple" := (North, Right 1) == (North, Right 1)
test "tuple, different" := Bool.not ((North, Right 1) == (North, Right 2))
test "list of trees" := [Node Leaf 1 Leaf, Leaf] == [Node Leaf 1 Leaf, Leaf]
test "list of trees, different" := Bool.not ([Node Leaf 1 Leaf, Leaf] == [Leaf, Leaf])

-- A record containing user types gets `==` too.
type Move = { dir : Dir, steps : Nat, path : Path }

def mv (n : Nat) : Move := { dir = North, steps = n, path = Step East Here }

test "record" := mv 2 == mv 2
test "record, different" := Bool.not (mv 2 == mv 3)

-- In a definition, too, not just at compile time.
def sameTree (t : Tree Dir) (u : Tree Dir) : Bool := t == u

test "at run time" := sameTree (Node Leaf East Leaf) (Node Leaf East Leaf)
test "at run time, different" := Bool.not (sameTree (Node Leaf East Leaf) (Node Leaf West Leaf))

-- The derived decider is a proof: `auto` runs it at compile time, so this
-- only compiles if it says `Yes`.
def needsEq (x : Tree Nat) (y : Tree Nat) : [auto h : x = y] -> Nat := 1

test "auto proof" := needsEq (Node Leaf 1 Leaf) (Node Leaf 1 Leaf) == 1

-- And a branch can use the equation it learns.
def pick (t : Tree Nat) (u : Tree Nat) : Nat :=
  if h : t = u then
    needsEq t u
  else
    0

test "if h, equal" := pick Leaf Leaf == 1
test "if h, different" := pick Leaf (Node Leaf 1 Leaf) == 0
