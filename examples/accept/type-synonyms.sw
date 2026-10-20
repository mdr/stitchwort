-- `type Name = T` is a transparent name for a type, exactly
-- `def Name: Type := T`: interchangeable with it, with its own namespace
-- for dot notation. `{` after `=` starts a record and `|` a sum type;
-- anything else is the type.
type Grid = List (List Nat)

def Grid.rolls (g: Grid): Nat := (g.map (row => row.length)).sum

type Matrix (a: Type) = List (List a)

def Matrix.rows (m: Matrix a): Nat := m.length

type Point = (Nat, Nat)

def origin: Point := (0, 0)

-- A `Grid` is a `List (List Nat)` and back.
def sample: Grid := [[1, 2], [3]]
def same: List (List Nat) := sample

test "dot notation through a synonym" := sample.rolls == 3
test "synonym with a parameter" := ([[True], [False]]: Matrix Bool).rows == 2
test "tuple synonym" := origin == (0, 0)
