-- Default values of record and constructor fields
-- (docs/proposals/named-arguments.md §5.1): `step: Nat := 1` in a record,
-- `(id: Text := "anonymous")` in a constructor. A literal or a named
-- construction may leave out a field that has one; positional calls and
-- named arguments still give every field.

import Std (Vec)

type RangeOptions = {
  start: Nat := 0,
  stop: Nat,
  step: Nat := 1
}

def bounds (options: RangeOptions): List Nat := [options.start, options.stop, options.step]

def small: RangeOptions := { stop = 10 }

test "left out fields are their defaults" :=
  small.start == 0 && small.step == 1 && small.stop == 10
test "a given field replaces its default" := bounds { stop = 10, step = 3 } == [0, 10, 3]
test "as a named argument" := bounds (options := { start = 2, stop = 5 }) == [2, 5, 1]

-- Leaving a field out is definitionally equal to giving its default.
theorem smallInFull: small = ({ start = 0, stop = 10, step = 1 }: RangeOptions) := rfl

-- A record whose fields all have defaults: `{}`.
type Style = { width: Nat := 80, indent: Nat := 2 }

def plain: Style := {}

test "every field left out" := plain.width == 80 && plain.indent == 2

-- A default may use earlier fields, and a later field's type may mention
-- a defaulted one: the default computes, so `{ cells = … }` with eight
-- cells fits.
type Sized = {
  size: Nat := 8,
  cells: Vec Bool size := Vec.replicate size False
}

def eight: Sized := {}
def three: Sized := { size = 3 }
def eightAgain: Sized := { cells = Vec.replicate 8 True }

test "dependent defaults" :=
  eight.cells.toList.length == 8 && three.cells.toList.length == 3
test "a later field fits the default" := eightAgain.size == 8

-- A default uses the actual value of the earlier field, never an assumed
-- default.
type Twice = { x: Nat, twice: Nat := x + x }

def tripled (n: Nat): Twice := { x = n * 3 }

test "the default sees the given field" := (tripled 2).twice == 12

-- An update keeps the value a field has: a default is a recipe for
-- building, not a computed property.
test "an update keeps fields" := ({ tripled 2 | x = 1 }).twice == 12

-- Patterns are unchanged: they name every field, or use `..`.
def total: Twice -> Nat
  | { x, twice } => x + twice

test "patterns name every field" := total (tripled 1) == 9

-- A type's parameters may appear in a default's type.
type Box (a: Type) = { item: a, label: Text := "box", extra: List a := [] }

def boxed: Box Nat := { item = 5 }

test "generic" := boxed.label == "box" && boxed.extra == []

-- Constructor fields: named construction leaves them out, positional and
-- named-argument calls give every field.
type Shape =
  | Circle (radius: Nat) (id: Text := "anonymous")
  | Square (side: Nat) (id: Text := "square")

def idOf (shape: Shape): Text := shape.id

test "named construction" := idOf (Circle { radius = 1 }) == "anonymous"
test "positional construction gives every field" := idOf (Circle 1 "c") == "c"
test "named arguments wait for every field" :=
  let waiting := Circle (radius := 1)
  idOf (waiting "d") == "d"
test "without an expected type" :=
  let made := Square { side = 2 }
  made == Square 2 "square"

-- An indexed family: implicit fields are inferred, defaults filled.
type Tower: Nat -> Type =
  | Ground (name: Text := "ground"): Tower 0
  | Floor [n: Nat] (below: Tower n) (name: Text := "floor"): Tower (Succ n)

def towerName (tower: Tower n): Text := tower.name

test "family" := towerName (Floor { below = Ground {} }) == "floor"

-- In a computation, a given field runs once, and the default uses its
-- result.
ability Log where
  say: Nat -> {Log} ()

def collect (program: () -> {Log | e} a): {e} (List Nat, a) :=
  handle program() with
    | return x => ([], x)
    | say n, k =>
      let rest := k()
      (Cons n rest.fst, rest.snd)

def given (n: Nat): {Log} Nat :=
  say n
  n

def logged(): {Log} Twice := { x = given 21 }

test "a given field runs once" := collect logged == ([21], { x = 21, twice = 42 })
