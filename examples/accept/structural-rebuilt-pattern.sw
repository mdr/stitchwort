-- Pairs with reject/termination-rebuilt-pattern.sw: a constructor rebuilt
-- from exactly the parts of a nested pattern is that part of the argument,
-- so recursion on it is structural, at any depth and for any data type.

def everyPair (check: Nat → Nat → Bool): (levels: List Nat) → Bool
  | [] => True
  | [x] => True
  | [x, y] => check x y
  | [x, y, z, ..more] => check x y && everyPair check [y, z, ..more]

theorem everyPairTrue (levels: List Nat): everyPair (x y => True) levels = True := match levels with
  | [] => rfl
  | [x] => rfl
  | [x, y] => rfl
  | [x, y, z, ..more] => everyPairTrue [y, z, ..more]

-- The same in a `match` after a `let`, which is lifted into a function of
-- its own: the patterns around it still count.
def risingPrefix: (levels: List Nat) → Nat
  | [] => 0
  | [x] => 0
  | [x, y] => if x < y then 1 else 0
  | [x, y, z, ..more] =>
    let later := risingPrefix [y, z, ..more]
    match x < y with
      | True => 1 + later
      | False => 0

theorem everyPairTrueLifted (levels: List Nat): everyPair (x y => True) levels = True := match levels with
  | [] => rfl
  | [x] => rfl
  | [x, y] => rfl
  | [x, y, z, ..more] =>
    let kept := everyPairTrueLifted [y, z, ..more]
    cases

type Tree: Type =
  | Leaf
  | Node (left: Tree) (value: Nat) (right: Tree)

-- The value at each node on the way down the left, each but the last.
def leftValues: Tree → List Nat
  | Leaf => []
  | Node Leaf value right => []
  | Node (Node (Node a b c) inner innerRight) value right =>
    [value, ..leftValues (Node (Node a b c) inner innerRight)]
  | Node (Node Leaf inner innerRight) value right => [value]

-- The length is an implicit field of `VCons`. In the rebuilt
-- `VCons y (VCons z rest)` it's filled in as one more than the inner
-- length, not as the pattern's own `n`; the tail's type pins it.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def sumFirsts: Vec Nat n → Nat
  | VNil => 0
  | VCons x VNil => x
  | VCons x (VCons y VNil) => x
  | VCons x (VCons y (VCons z rest)) => x + sumFirsts (VCons y (VCons z rest))

-- An implicit type field, filled in from the rebuilt list's type (paired with
-- soundness/rebuilt-with-other-type.sw).
type Box: Type 1 =
  | Stop
  | Mk [a: Type] (xs: List a) (rest: Box)

def nonEmptyRun: Box → Nat
  | Mk [x, ..xs] (Mk [y, ..ys] rest) => Succ (nonEmptyRun (Mk [y, ..ys] rest))
  | other => 0

test "sumFirsts adds all but the last" := sumFirsts (VCons 1 (VCons 2 (VCons 3 VNil))) == 3
test "leftValues" := leftValues (Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf) == [1, 2]
test "everyPair" := everyPair (x y => x < y) [1, 2, 3]
test "risingPrefix" := risingPrefix [1, 2, 3, 1] == 2
