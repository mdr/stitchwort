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
type Tree: Type =
  | Node (label: Nat) (kids: Forest)

type Forest: Type =
  | FNil
  | FCons (first: Tree) (rest: Forest)

-- The number of nodes. `kids` is part of the `Tree` that `size` matched, so
-- `sizeForest kids` is a smaller call, even though it's another type.
def size: Tree -> Nat
  | Node n kids => Succ (sizeForest kids)

def sizeForest: Forest -> Nat
  | FNil       => 0
  | FCons t ts => size t + sizeForest ts

-- Adding up the labels.
def sumTree: Tree -> Nat
  | Node n kids => n + sumForest kids

def sumForest: Forest -> Nat
  | FNil       => 0
  | FCons t ts => sumTree t + sumForest ts

def mapTree (f: Nat -> Nat): Tree -> Tree
  | Node n kids => Node (f n) (mapForest f kids)

def mapForest (f: Nat -> Nat): Forest -> Forest
  | FNil       => FNil
  | FCons t ts => FCons (mapTree f t) (mapForest f ts)

def leaf (n: Nat): Tree := Node n FNil

def example: Tree := Node 1 (FCons (leaf 2) (FCons (Node 3 (FCons (leaf 4) FNil)) FNil))

test "size" := size example == 4
test "sum" := sumTree example == 10
test "map" := sumTree (mapTree (\n => n + 1) example) == 14

-- Proofs by mutual induction over the two types: mapping changes no sizes.
theorem sizeMap (f: Nat -> Nat): (t: Tree) -> size (mapTree f t) = size t
  | Node n kids => Eq.cong Succ (sizeMapForest f kids)

theorem sizeMapForest (f: Nat -> Nat): (ts: Forest) ->
    sizeForest (mapForest f ts) = sizeForest ts
  | FNil       => rfl
  | FCons t ts =>
    Eq.trans (Eq.cong (\a => a + sizeForest (mapForest f ts)) (sizeMap f t))
          (Eq.cong (\b => size t + b) (sizeMapForest f ts))

-- Every tree has at least one node.
theorem sizeNotZero: (t: Tree) -> Not (size t = 0)
  | Node n kids, a1 => Nat.succNotZero (sizeForest kids) a1

-- Even and odd numbers, as data: each is the successor of the other kind.
type Even: Type =
  | EZero
  | ESucc (pred: Odd)

type Odd: Type =
  | OSucc (pred: Even)

def evenToNat: Even -> Nat
  | EZero   => 0
  | ESucc o => Succ (oddToNat o)

def oddToNat: Odd -> Nat
  | OSucc e => Succ (evenToNat e)

def isEven: Nat -> Bool
  | 0      => True
  | Succ n => isOdd n

def isOdd: Nat -> Bool
  | 0      => False
  | Succ n => isEven n

theorem evenIsEven: (e: Even) -> isEven (evenToNat e) = True
  | EZero   => rfl
  | ESucc o => oddIsOdd o

theorem oddIsOdd: (o: Odd) -> isOdd (oddToNat o) = True
  | OSucc e => evenIsEven e

test "three" := oddToNat (OSucc (ESucc (OSucc EZero))) == 3

-- The same as propositions. Matching on one proof to produce another is
-- fine (here, by mutual recursion over the proofs); producing data from one
-- isn't (reject/mutual-prop-elim.sw).
type EvenP: Prop =
  | EvenZero
  | EvenSucc (pred: OddP)

type OddP: Prop =
  | OddSucc (pred: EvenP)

theorem evenTrivial: EvenP -> Unit
  | EvenZero   => Trivial
  | EvenSucc o => oddTrivial o

theorem oddTrivial: OddP -> Unit
  | OddSucc e => evenTrivial e

-- The types of a group may take parameters: the same ones, in the same
-- order, which the fields use exactly as given.
type Rose (a: Type): Type =
  | Bloom (value: a) (kids: Roses a)

type Roses (a: Type): Type =
  | NoRoses
  | MoreRoses (first: Rose a) (rest: Roses a)

def flatten: Rose a -> List a
  | Bloom x kids => Cons x (flattenAll kids)

def flattenAll: Roses a -> List a
  | NoRoses        => Nil
  | MoreRoses r rs => (flatten r).append (flattenAll rs)

test "flatten" := (flatten (Bloom 1 (MoreRoses (Bloom 2 NoRoses) (MoreRoses (Bloom 3 NoRoses) NoRoses)))).length == 3

-- A sibling may be the result of a function field. Calling it gives a part
-- of the matched value, so it's a smaller argument.
type Branching: Type =
  | Tip
  | Fork (width: Nat) (child: Nat -> Layer)

type Layer: Type =
  | MkLayer (label: Nat) (below: Branching)

def depth: Branching -> Nat -> Nat
  | Tip, n => 0
  | Fork w child, n => Succ (layerDepth (child n) n)

def layerDepth: Layer -> Nat -> Nat
  | MkLayer l b, n => depth b n

-- Three types in one group.
type Expr: Type =
  | Num (n: Nat)
  | Block (body: Stmts) (result: Expr)

type Stmt: Type =
  | Assign (value: Expr)
  | Nested (body: Stmts)

type Stmts: Type =
  | Finished
  | Then (first: Stmt) (rest: Stmts)

def exprCount: Expr -> Nat
  | Num n     => 1
  | Block b r => stmtsCount b + exprCount r + 1

def stmtCount: Stmt -> Nat
  | Assign e => exprCount e
  | Nested b => stmtsCount b

def stmtsCount: Stmts -> Nat
  | Finished => 0
  | Then s r => stmtCount s + stmtsCount r

test "count" := exprCount (Block (Then (Assign (Num 1)) (Then (Nested Finished) Finished)) (Num 2)) == 3
