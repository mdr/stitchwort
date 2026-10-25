-- A lambda argument whose parameter type isn't known yet when it's reached
-- is checked after the later arguments (docs/syntax.md, "Lambdas"): in
-- `List.map people (p => p.name)`, `people` fixes `p`'s type first. Only
-- the checking order changes; the arguments are passed as written.

import Std (IO, List)

type Person = { name: Text, age: Nat }

type Entry = { position: Nat, label: Text }

def people: List Person := [{ name = "Ann", age = 30 }, { name = "Bo", age = 4 }]

def entries: List Entry := [{ position = 1, label = "a" }, { position = 5, label = "b" }]

def names: List Text := List.map people (p => p.name)

test "map with a lambda before the list" := names == ["Ann", "Bo"]

def early: List Entry := List.filter entries (x => x.position < 3)

test "filter with a lambda before the list" := List.map early (e => e.label) == ["a"]

def total: Nat := List.foldLeft people 0 (acc p => acc + p.age)

test "a fold whose lambda comes before the start and the list" := total == 34

-- Nested: the outer lambda waits for `groups`, then the inner one for `g`.
def groups: List (List Person) := [people, [{ name = "Cy", age = 7 }]]

def nested: List (List Nat) := List.map groups (g => List.map g (p => p.age))

test "nested lambdas" := nested == [[30, 4], [7]]

-- A lambda that already worked in place is checked in place, as before.
def doubled: List Nat := List.map [1, 2, 3] (x => x * 2)

test "a lambda that needs no waiting" := doubled == [2, 4, 6]

-- The same holds when the callback is effectful (SW-30): `p` fixes `q`.
def appIO (f: a → {IO} b) (x: a): {IO} b := f x

def nameIO (p: Person): {IO} Text := appIO (q => q.name) p

-- ... and in a pure call that follows an effectful statement.
def appP (f: a → b) (x: a): b := f x

def nameAfterPrint (p: Person): {IO} Text :=
  IO.print "x"
  appP (q => q.name) p
