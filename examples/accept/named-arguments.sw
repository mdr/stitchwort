-- Named arguments (docs/proposals/named-arguments.md §4): `(x := e)` names
-- an explicit parameter and `[x := e]` an implicit one, in any order and
-- mixed with positional arguments. The call is the positional one.

import Std (Vec)

def between (low: Nat) (high: Nat): Nat := high - low

def clampTo (low: Nat) (high: Nat) (value: Nat): Nat :=
  if value < low then low else if value > high then high else value

def place (x: Nat) (y: Nat): Nat := x * 10 + y

def pick [count: Nat] [label: Text] (x: Nat): Nat := x + count

-- Any order, mixed with positional arguments.
test "names in any order" := between (high := 9) (low := 3) == between 3 9
test "positional then named" := between 3 (high := 9) == 6

-- Slots fill in written order (D1112): a positional argument takes the
-- first explicit parameter still free.
test "named first, positional fills the rest" := place (y := 2) 1 == 12
test "positional first, named fills the rest" := place 1 (y := 2) == 12
test "split anywhere" := (place (y := 2)) 1 == 12

-- Named implicit arguments in any order (D1094).
test "implicits in any order" := pick [label := "a"] [count := 3] 1 == 4
test "implicits in order" := pick [count := 3] [label := "a"] 1 == 4

-- A parameter left out before one given makes a function of it (D1095).
test "a function of the missing parameters" :=
  [1, 50, 200].map (clampTo (low := 5) (high := 100)) == [5, 50, 100]
test "leaving out the first" := (clampTo (high := 10)) 0 20 == 10

-- Its parameters keep their names.
def atMostTen: (low: Nat) -> (value: Nat) -> Nat := clampTo (high := 10)
test "names after a skip" := atMostTen (value := 50) (low := 0) == 10
test "names of a call with a skip" := (clampTo (high := 10)) (value := 4) (low := 5) == 5

-- A missing parameter is a variable: the arguments after it may depend on
-- it, as an implicit inserted for it does (§4.5 R4).
def total (n: Nat) (xs: Vec Nat n): Nat := n + Vec.length xs
def zeros [n: Nat]: Vec Nat n := Vec.replicate n 0
test "a later argument uses the missing one" := (total (xs := zeros)) 2 == 4

-- Where the names come from (§4.3).
def Picker: Type := [count: Nat] -> (x: Nat) -> Nat
def usePicker (h: Picker): Nat := h (x := 1) [count := 3]

def annotated: Nat :=
  let g: (start: Nat) -> (stop: Nat) -> Nat := between
  g (stop := 9) (start := 3)
test "an annotation names the parameters" := annotated == 6

def aliased: Nat :=
  let g := between
  g (high := 9) (low := 3)
test "a let without an annotation keeps the names" := aliased == 6

def partially: Nat :=
  let g := clampTo 0
  g (value := 50) (high := 10)
test "a partial application keeps the rest of the names" := partially == 10

def annotatedValue: Nat := (between: (from: Nat) -> (to: Nat) -> Nat) (to := 9) (from := 3)
test "an annotated expression" := annotatedValue == 6

-- A variable in a named type argument is bound automatically, as it is in
-- the argument's position.
def Matrix (a: Type): Type := List (List a)
def rowCount (m: Matrix (a := a)): Nat := m.length
test "a variable bound from a named type argument" := rowCount [[1], [2]] == 2

-- Constructors (D1096).
type Shape =
  | Circle (radius: Nat) (id: Text)
  | Square (side: Nat)

test "a constructor by name" := Circle (id := "a") (radius := 1) == Circle 1 "a"
test "a constructor with a field left out" :=
  ["a", "b"].map (Circle (radius := 2)) == [Circle 2 "a", Circle 2 "b"]

-- Dot notation: the receiver fills its parameter first.
type Point = { x: Nat, y: Nat }

def Point.scale (point: Point) (by: Nat) (plus: Nat): Point :=
  { x = point.x * by + plus, y = point.y * by + plus }

def Point.shift (dx: Nat) (dy: Nat) (point: Point): Point :=
  { x = point.x + dx, y = point.y + dy }

def corner: Point := { x = 1, y = 5 }

test "dot notation by name" := corner.scale (plus := 1) (by := 2) == corner.scale 2 1
test "dot notation with a parameter left out" := (corner.scale (plus := 1)) 2 == corner.scale 2 1

-- Method sections, and pipes.
test "a named section" :=
  [corner].map (.shift (dy := 1) (dx := 2)) == [corner].map (.shift 2 1)
test "a section of the library" := "a,b".split (separator := ',') == "a,b".split ','
test "a pipe fills the first free parameter" := (5 |> clampTo (low := 0) (high := 3)) == 3
test "a pipe after a named argument" := (20 |> clampTo (high := 10) (low := 0)) == 10

-- Proofs see the positional term.
theorem namedIsPositional (low: Nat) (high: Nat):
    between (high := high) (low := low) = between low high := rfl
