-- Data types whose constructors mention each other
-- (docs/proposals/mutual-recursion.md §7). Types that refer to each other are
-- checked together: they share one list of parameters and one universe, and
-- strict positivity is checked across all of them. Functions and proofs over
-- them are groups of definitions, and a field of a sibling type matched out
-- of an argument is smaller than it. Pairs with
-- soundness/mutual-non-positive.sw, reject/mutual-sibling-constructor.sw and
-- reject/mutual-prop-elim.sw.

-- A tree whose children are a forest, and a forest of trees. Written in
-- either order.
type Tree : Type =
  | Node (label : Nat) (kids : Forest)

type Forest : Type =
  | FNil
  | FCons (first : Tree) (rest : Forest)

-- The number of nodes. `kids` is part of the `Tree` that `size` matched, so
-- `sizeForest kids` is a smaller call, even though it's another type.
size : Tree -> Nat
size (Node n kids) = Succ (sizeForest kids)

sizeForest : Forest -> Nat
sizeForest FNil         = 0
sizeForest (FCons t ts) = size t + sizeForest ts

-- Adding up the labels.
sumTree : Tree -> Nat
sumTree (Node n kids) = n + sumForest kids

sumForest : Forest -> Nat
sumForest FNil         = 0
sumForest (FCons t ts) = sumTree t + sumForest ts

mapTree : (Nat -> Nat) -> Tree -> Tree
mapTree f (Node n kids) = Node (f n) (mapForest f kids)

mapForest : (Nat -> Nat) -> Forest -> Forest
mapForest f FNil         = FNil
mapForest f (FCons t ts) = FCons (mapTree f t) (mapForest f ts)

leaf : Nat -> Tree
leaf n = Node n FNil

example : Tree
example = Node 1 (FCons (leaf 2) (FCons (Node 3 (FCons (leaf 4) FNil)) FNil))

test "size" = size example == 4
test "sum" = sumTree example == 10
test "map" = sumTree (mapTree (\n -> n + 1) example) == 14

-- Proofs by mutual induction over the two types: mapping changes no sizes.
theorem sizeMap : (f : Nat -> Nat) -> (t : Tree) -> size (mapTree f t) = size t
sizeMap f (Node n kids) = cong Succ (sizeMapForest f kids)

theorem sizeMapForest : (f : Nat -> Nat) -> (ts : Forest) ->
  sizeForest (mapForest f ts) = sizeForest ts
sizeMapForest f FNil         = rfl
sizeMapForest f (FCons t ts) =
  trans (cong (\a -> a + sizeForest (mapForest f ts)) (sizeMap f t))
        (cong (\b -> size t + b) (sizeMapForest f ts))

-- Every tree has at least one node.
theorem sizeNotZero : (t : Tree) -> Not (size t = 0)
sizeNotZero (Node n kids) = succNotZero (sizeForest kids)

-- Even and odd numbers, as data: each is the successor of the other kind.
type Even : Type =
  | EZero
  | ESucc (pred : Odd)

type Odd : Type =
  | OSucc (pred : Even)

evenToNat : Even -> Nat
evenToNat EZero     = 0
evenToNat (ESucc o) = Succ (oddToNat o)

oddToNat : Odd -> Nat
oddToNat (OSucc e) = Succ (evenToNat e)

isEven : Nat -> Bool
isEven 0        = True
isEven (Succ n) = isOdd n

isOdd : Nat -> Bool
isOdd 0        = False
isOdd (Succ n) = isEven n

theorem evenIsEven : (e : Even) -> isEven (evenToNat e) = True
evenIsEven EZero     = rfl
evenIsEven (ESucc o) = oddIsOdd o

theorem oddIsOdd : (o : Odd) -> isOdd (oddToNat o) = True
oddIsOdd (OSucc e) = evenIsEven e

test "three" = oddToNat (OSucc (ESucc (OSucc EZero))) == 3

-- The same as propositions. Matching on one proof to produce another is
-- fine (here, by mutual recursion over the proofs); producing data from one
-- isn't (reject/mutual-prop-elim.sw).
type EvenP : Prop =
  | EvenZero
  | EvenSucc (pred : OddP)

type OddP : Prop =
  | OddSucc (pred : EvenP)

theorem evenTrivial : EvenP -> Unit
evenTrivial EvenZero     = Trivial
evenTrivial (EvenSucc o) = oddTrivial o

theorem oddTrivial : OddP -> Unit
oddTrivial (OddSucc e) = evenTrivial e

-- The types of a group may take parameters: the same ones, in the same
-- order, which the fields use exactly as given.
type Rose (a : Type) : Type =
  | Bloom (value : a) (kids : Roses a)

type Roses (a : Type) : Type =
  | NoRoses
  | MoreRoses (first : Rose a) (rest : Roses a)

flatten : Rose a -> List a
flatten (Bloom x kids) = Cons x (flattenAll kids)

flattenAll : Roses a -> List a
flattenAll NoRoses          = Nil
flattenAll (MoreRoses r rs) = append (flatten r) (flattenAll rs)

test "flatten" = length (flatten (Bloom 1 (MoreRoses (Bloom 2 NoRoses) (MoreRoses (Bloom 3 NoRoses) NoRoses)))) == 3

-- A sibling may be the result of a function field. Calling it gives a part
-- of the matched value, so it's a smaller argument.
type Branching : Type =
  | Tip
  | Fork (width : Nat) (child : Nat -> Layer)

type Layer : Type =
  | MkLayer (label : Nat) (below : Branching)

depth : Branching -> Nat -> Nat
depth Tip          n = 0
depth (Fork w child) n = Succ (layerDepth (child n) n)

layerDepth : Layer -> Nat -> Nat
layerDepth (MkLayer l b) n = depth b n

-- Three types in one group.
type Expr : Type =
  | Num (n : Nat)
  | Block (body : Stmts) (result : Expr)

type Stmt : Type =
  | Assign (value : Expr)
  | Nested (body : Stmts)

type Stmts : Type =
  | Finished
  | Then (first : Stmt) (rest : Stmts)

exprCount : Expr -> Nat
exprCount (Num n)     = 1
exprCount (Block b r) = stmtsCount b + exprCount r + 1

stmtCount : Stmt -> Nat
stmtCount (Assign e) = exprCount e
stmtCount (Nested b) = stmtsCount b

stmtsCount : Stmts -> Nat
stmtsCount Finished   = 0
stmtsCount (Then s r) = stmtCount s + stmtsCount r

test "count" = exprCount (Block (Then (Assign (Num 1)) (Then (Nested Finished) Finished)) (Num 2)) == 3
