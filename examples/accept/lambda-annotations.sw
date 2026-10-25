-- A lambda's parameter may have a written type, as a definition's does:
-- `(x: T) => e`. The annotation gives dot notation the type it needs, and
-- lets a lambda be inferred with no expected type.

import List (map)
import Std (List)

type Person = { name: Text, age: Nat }

-- No expected type: the lambda's type is inferred from its annotation.
-- (A `def` needs its type written, so these are `let`s in a test.)
test "inferred" :=
  let nameOf := (p: Person) => p.name
  let ageOf := (p: Person) => p.age
  let ada: Person := { name = "Ada", age = 36 }
  nameOf ada == "Ada" ∧ ageOf ada == 36

-- Applied on the spot.
test "applied" := ((p: Person) => p.name) { name = "Ada", age = 36 } == "Ada"

-- Several parameters, each in its own brackets, or grouped like a header's.
test "multiple" :=
  let add := (x: Nat) (y: Nat) => x + y
  let addGrouped := (x y: Nat) => x + y
  add 2 3 == 5 ∧ addGrouped 4 5 == 9

-- Mixed with plain names and patterns.
def mixed: Nat → Nat → Nat := x (y: Nat) => x + y

def mixedBack: Nat → Nat → Nat := (x: Nat) y => x + y

def withPair: (Nat, Nat) → Nat → Nat := (a, b) (c: Nat) => a + b + c

test "mixed" := mixed 1 2 == 3 ∧ mixedBack 1 2 == 3 ∧ withPair (1, 2) 3 == 6

-- Checked against an expected type that agrees with the annotation.
def inc: Nat → Nat := (n: Nat) => n + 1

-- Inside `List.map` and `|>`.
def names (people: List Person): List Text :=
  List.map people ((p: Person) => p.name)

def ages (people: List Person): List Nat :=
  people |> List.map ((p: Person) => p.age)

def piped (p: Person): Text := p |> (q: Person) => q.name

test "map" :=
  names [{ name = "Ada", age = 36 }, { name = "Bo", age = 20 }] == ["Ada", "Bo"]

test "pipe" := ages [{ name = "Ada", age = 36 }] == [36]
test "pipe lambda" := piped { name = "Ada", age = 36 } == "Ada"
