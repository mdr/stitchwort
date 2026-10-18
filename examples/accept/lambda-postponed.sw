-- A lambda argument whose parameter type isn't known yet when it's reached
-- is checked after the later arguments (docs/syntax.md, "Lambdas"): in
-- `List.map (\p => p.name) people`, `people` fixes `p`'s type first. Only
-- the checking order changes; the arguments are passed as written.

type Person = { name : Text, age : Nat }

type Entry = { position : Nat, label : Text }

def people : List Person := [{ name = "Ann", age = 30 }, { name = "Bo", age = 4 }]

def entries : List Entry := [{ position = 1, label = "a" }, { position = 5, label = "b" }]

def names : List Text := List.map (\p => p.name) people

test "map with a lambda before the list" := names == ["Ann", "Bo"]

def early : List Entry := List.filter (\x => x.position < 3) entries

test "filter with a lambda before the list" := List.map (\e => e.label) early == ["a"]

def total : Nat := List.foldl (\acc p => acc + p.age) 0 people

test "a fold whose lambda comes before the start and the list" := total == 34

-- Nested: the outer lambda waits for `groups`, then the inner one for `g`.
def groups : List (List Person) := [people, [{ name = "Cy", age = 7 }]]

def nested : List (List Nat) := List.map (\g => List.map (\p => p.age) g) groups

test "nested lambdas" := nested == [[30, 4], [7]]

-- A lambda that already worked in place is checked in place, as before.
def doubled : List Nat := List.map (\x => x * 2) [1, 2, 3]

test "a lambda that needs no waiting" := doubled == [2, 4, 6]
