-- Chapter 4: functions.
import Std (List, Nat, Option, Text)

-- begin lambdas
def increment: Nat → Nat := n => n + 1

def add: Nat → Nat → Nat := a b => a + b

def addTen: Nat → Nat := add 10

test "lambdas" := [1, 2, 3].map (n => n * n) == [1, 4, 9]
test "partial application" := addTen 5 == 15
test "a constructor is a function" := [1, 2].map Some == [Some 1, Some 2]
-- end lambdas

-- begin generics
def twice (f: a → a) (x: a): a := f (f x)

def firstOr (fallback: a): List a → a
  | [] => fallback
  | [x, .._] => x

test "twice" := twice increment 5 == 7
test "a is Text here" := firstOr "none" ["tea", "milk"] == "tea"
-- end generics

-- begin implicit
def pairUp [a b: Type] (x: a) (y: b): (a, b) := (x, y)

test "implicit arguments are inferred" := pairUp 1 "one" == (1, "one")
test "or given by name" := pairUp [b := Text] 1 "one" == (1, "one")
-- end implicit

-- begin implicit-lambda
def pairUpLambda: [a: Type] → [b: Type] → a → b → (a, b) := [a b: Type] (x: a) (y: b) => (x, y)

test "a lambda with implicit parameters" :=
  let flip := [a b: Type] (x: a) (y: b) => (y, x)
  flip 1 "one" == ("one", 1) ∧ pairUpLambda 1 "one" == (1, "one")
-- end implicit-lambda

-- begin named
def clamp (low high value: Nat): Nat := if value < low then low else if value > high then high else value

test "by position" := clamp 0 10 50 == 10
test "by name, in any order" := clamp (value := 50) (high := 10) (low := 0) == 10
test "leaving some out" := [1, 50, 200].map (clamp (low := 5) (high := 100)) == [5, 50, 100]
-- end named

-- begin named-constructors
type Pair (a: Type) (b: Type) = | MkPair (first: a) (second: b)

test "an empty list of integers" := (Nil [a := Int]).length == 0
test "the type's parameters by name" := MkPair [b := Text] [a := Int] 1 "one" == MkPair (1: Int) "one"
-- end named-constructors

-- begin param-defaults
def price (base: Nat) (quantity: Nat := 1) (discount: Nat := 0): Nat := base * quantity - discount

test "defaults" := price 5 == 5
test "some by name" := price 5 (quantity := 3) == 15
test "any order" := price 5 (discount := 2) (quantity := 3) == 13
test "a call that leaves them out is a function of the rest" := [5, 8].map price == [5, 8]
-- end param-defaults

-- begin dot
type Point = { x: Int, y: Int }

def Point.shift (point: Point) (dx dy: Int): Point := { x = point.x + dx, y = point.y + dy }

def Point.manhattan (point: Point): Nat := point.x.natAbs + point.y.natAbs

def origin: Point := { x = 0, y = 0 }

test "dot notation" := (origin.shift 3 (-4)).manhattan == 7
test "the same call, in full" := Point.manhattan (Point.shift origin 3 (-4)) == 7
-- end dot

-- begin pipes
def wordLengths (line: Text): List Nat := line |> .split ' ' |> .filter (word => word ≠ "") |> .map .length

test "pipes" := wordLengths "the  quick fox" == [3, 5, 3]
-- end pipes

-- begin pipe-precedence
test "compare a pipeline" := [1, 2, 3, 4] |> List.filter (n => n % 2 == 0) == [2, 4]
test "a pipe after ∧" := wordLengths "" == [] ∧ ["a", "b"] |> .length == 2
-- end pipe-precedence

-- begin sections
def distances (points: List Point): List Nat := points.map .manhattan

test "a section is a function" := distances [origin, { x = 1, y = -2 }] == [0, 3]
test "with arguments" := ["a,b", "c"].map (.split ',') == [["a", "b"], ["c"]]
test "a section runs to the end of the expression" := ["ab", "", "c"].filter (.length > 1) == ["ab"]
test "an operator section" := [1, 5, 2, 8].filter (> 3) == [5, 8]
test "the argument on the right" := [1, 2].map (10 +) == [11, 12]
test "a bare operator" := [1, 2, 3].foldLeft 0 (+) == 6
-- end sections

-- begin local
def sumOfSquares (n: Nat): Nat :=
  def go: Nat → Nat → Nat
    | 0, total => total
    | Succ k, total => go k (total + Succ k * Succ k)
  go n 0

test "local definition" := sumOfSquares 3 == 14
test "named from outside" := sumOfSquares.go 2 0 == 5
-- end local

-- begin clauses
type Reading = | Valid (value: Nat) | Garbled (text: Text) | Missing

def Reading.score: Reading → Nat := match
  | Valid value => value
  | Garbled text => text.length
  | Missing => 0

def valid: Reading → Option Nat := match some | Valid value => value

def isMissing: Reading → Bool := matches | Missing

def sample: List Reading := [Valid 4, Garbled "xx", Missing, Valid 9]

test "a lambda written as its cases" :=
  sample.map (match
    | Valid value => value
    | _ => 0)
    == [4, 0, 0, 9]
test "a definition written as cases" := sample.map Reading.score == [4, 2, 0, 9]
test "keeping what matches" := sample.filterMap valid == [4, 9]
test "inline" := sample.filterMap (match some | Garbled text => text.length) == [2]
test "the first match" := sample.findMap (match some | Valid value => value * 10) == Some 40
test "testing a value" := sample.filter (matches | Valid _ | Missing) == [Valid 4, Missing, Valid 9]
test "a name is tested" := sample.count isMissing == 1

def bigValue: Reading → Option Nat := match some | Valid value if value > 5 => value

test "a condition on a case" := sample.filterMap bigValue == [9]

def isBig: Reading → Bool := matches | Valid value if value > 5

test "a condition alone" := sample.filter isBig == [Valid 9]
-- end clauses

-- begin higher-order
def applyAll (functions: List (Nat → Nat)) (start: Nat): Nat := functions.foldLeft start (value f => f value)

test "functions are values" := applyAll [increment, add 10, n => n * 2] 1 == 24
-- end higher-order
