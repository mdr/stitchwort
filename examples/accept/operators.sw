-- Operators through dictionaries (docs/proposals/interfaces.md §5.13):
-- `+` is `Add.add`, `*` is `Mul.mul`, and `<` and `<=` are `Ord`'s
-- `lessThan` and `lessEq`, from the instance found for the operands' type.
-- On `Nat` and `Int` that's the library's instances, so the terms are the
-- built-in operations, as before.

import Std (Bool, Eq, Int, List, Nat)

-- A user's type with `+`: an `Add` instance, with its laws.
type Point = { x: Int, y: Int }

def Point.add (p: Point) (q: Point): Point := { x = p.x + q.x, y = p.y + q.y }

def Point.origin: Point := { x = 0, y = 0 }

theorem Point.zeroAdd: (p: Point) -> Point.add Point.origin p = p
  | { x, y } => rewrite Int.zeroAdd x, Int.zeroAdd y in rfl

theorem Point.assoc (p: Point) (q: Point) (r: Point): Point.add (Point.add p q) r = Point.add p (Point.add q r) :=
  rewrite Int.addAssoc p.x q.x r.x, Int.addAssoc p.y q.y r.y in rfl

theorem Point.comm (p: Point) (q: Point): Point.add p q = Point.add q p :=
  rewrite Int.addComm p.x q.x, Int.addComm p.y q.y in rfl

instance Point.instAdd: Add Point :=
  { zero = Point.origin, add = Point.add, zeroAdd = Point.zeroAdd, assoc = Point.assoc, comm = Point.comm }

def p: Point := { x = 1, y = 2 }
def q: Point := { x = 10, y = -5 }

test "points add" := (p + q).x == 11 && (p + q).y == -3

-- Generic code: `+` and `*` on any type with the instance. There are no
-- generic literals; `Add.zero` and `Mul.one` stand for 0 and 1.
def twice [auto add: Add a] (x: a): a := x + x

def square [auto mul: Mul a] (x: a): a := x * x

def sumSquares [auto add: Add a] [auto mul: Mul a] (xs: List a): a :=
  xs.foldLeft (acc x => acc + x * x) Add.zero

test "twice" := (twice p).y == 4 && twice 21 == 42 && twice (-4: Int) == -8
test "square" := square 7 == 49 && square (-3: Int) == 9
test "sum of squares" := sumSquares [1, 2, 3] == 14 && sumSquares [(-1: Int), 2] == 5

-- `List.sum` is generic too.
test "sums" := [p, q, p].sum.x == 12 && [1, 2, 3].sum == 6 && [(3: Int), -5, 1].sum == -1
test "products" := [2, 3, 4].product == 24 && [(-2: Int), 3].product == -6

-- A law from the dictionary: the sum of two lists of points.
theorem pointsAppend (xs: List Point) (ys: List Point): (List.append xs ys).sum = xs.sum + ys.sum :=
  List.sumAppend xs ys

-- Comparisons on any type with `Ord`; `if` decides them with the decider
-- from the same dictionary (§5.16).
def before [auto ord: Ord a] (x: a) (y: a): Bool :=
  if x < y then True else False

def beforeNat [auto ord: Ord Nat] (x: Nat) (y: Nat): Bool :=
  if x < y then True else False

-- A predicate behind a definition: unfolded, then decided the same way.
def Below [auto ord: Ord a] (x: a) (y: a): Prop := x < y

def below [auto ord: Ord a] (x: a) (y: a): Bool := if Below x y then True else False

-- A named alternative with its own relations and deciders.
def descending: Ord Nat := {
  compare = x y => Nat.compare y x,
  lessThan = x y => Nat.LessThan y x,
  lessEq = x y => Nat.LessEq y x,
  decLessThan = x y => Nat.decLessThan y x,
  decLessEq = x y => Nat.decLessEq y x,
  equal = x y h => Eq.sym (Nat.compareEqual y x h),
  flip = x y => Nat.compareFlip y x,
  trans = x y z h1 h2 => Nat.compareTrans z y x h2 h1,
  lessThanOf = x y => Nat.lessOfCompare y x,
  lessThanTo = x y => Nat.compareOfLess y x,
  lessEqOf = x y => Nat.leOfCompare y x,
  lessEqTo = x y => Nat.compareOfLe y x
}

-- Generalising a function's type doesn't change what it does: `before` and
-- `beforeNat` agree, with the library's order and with `descending`.
test "before" := before 1 2 && beforeNat 1 2 && before "a" "b" && Bool.not (before 2 1)
test "descending" :=
  Bool.not (before [ord := descending] 1 2) && Bool.not (beforeNat [ord := descending] 1 2)
    && before [ord := descending] 2 1 && beforeNat [ord := descending] 2 1
test "below" := below 1 2 && Bool.not (below [ord := descending] 1 2) && Bool.not (below "b" "a")

-- On `Nat`, exactly the term it always was: `Nat.decLessThan x y`.
def least (x: Nat) (y: Nat): Nat := if x < y then x else y

test "least" := least 3 2 == 2 && least 2 3 == 2

-- `<` on text and lists, through their `Ord` instances.
test "text" := if "apple" < "banana" then True else False
test "lists" := if [1, 2] <= [1, 3] then True else False
