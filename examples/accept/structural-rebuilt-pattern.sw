-- Pairs with reject/termination-rebuilt-pattern.sw: a constructor rebuilt
-- from exactly the parts of a nested pattern is that part of the argument,
-- so recursion on it is structural, at any depth and for any data type.

def everyPair (check: Nat → Nat → Bool): (levels: List Nat) → Bool
  | Nil => True
  | Cons x Nil => True
  | Cons x (Cons y Nil) => check x y
  | Cons x (Cons y (Cons z more)) => check x y && everyPair check (Cons y (Cons z more))

theorem everyPairTrue: (levels: List Nat) → everyPair (x y => True) levels = True
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons y Nil) => rfl
  | Cons x (Cons y (Cons z more)) => everyPairTrue (Cons y (Cons z more))

-- The same in a `match` after a `let`, which is lifted into a function of
-- its own: the patterns around it still count.
def risingPrefix: (levels: List Nat) → Nat
  | Nil => 0
  | Cons x Nil => 0
  | Cons x (Cons y Nil) => if x < y then 1 else 0
  | Cons x (Cons y (Cons z more)) =>
    let later := risingPrefix (Cons y (Cons z more))
    match x < y with
      | True => 1 + later
      | False => 0

theorem everyPairTrueLifted: (levels: List Nat) → everyPair (x y => True) levels = True
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons y Nil) => rfl
  | Cons x (Cons y (Cons z more)) =>
    let kept := everyPairTrueLifted (Cons y (Cons z more))
    cases

type Tree: Type =
  | Leaf
  | Node (left: Tree) (value: Nat) (right: Tree)

-- The value at each node on the way down the left, each but the last.
def leftValues: Tree → List Nat
  | Leaf => Nil
  | Node Leaf value right => Nil
  | Node (Node (Node a b c) inner innerRight) value right =>
    Cons value (leftValues (Node (Node a b c) inner innerRight))
  | Node (Node Leaf inner innerRight) value right => Cons value Nil

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
  | Mk (Cons x xs) (Mk (Cons y ys) rest) => Succ (nonEmptyRun (Mk (Cons y ys) rest))
  | other => 0

test "sumFirsts adds all but the last" := sumFirsts (VCons 1 (VCons 2 (VCons 3 VNil))) == 3
test "leftValues" := leftValues (Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf) == Cons 1 (Cons 2 Nil)
test "everyPair" := everyPair (x y => x < y) (Cons 1 (Cons 2 (Cons 3 Nil)))
test "risingPrefix" := risingPrefix (Cons 1 (Cons 2 (Cons 3 (Cons 1 Nil)))) == 2
