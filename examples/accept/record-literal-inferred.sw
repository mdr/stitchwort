-- A record literal where nothing says its type is the one record type in
-- scope with exactly its fields, in any order; a type's parameters are
-- inferred from the fields.

type Position = { row: Int, column: Int }

type Robot = { position: Position, name: Text }

type Boxed (a: Type) = { contents: a, label: Text }

def start (row: Int): Robot :=
  let position := { column = 0, row }
  let robot := { name = "R", position }
  robot

test "the type comes from the fields" := (start 3).position.row == 3

test "a parameter is inferred" := ({ label = "n", contents = 5 }).contents == 5

test "in a list" := [{ row = 1, column = 2 }, { column = 3, row = 4 }].map (p => p.row) == [1, 4]

-- Where another part says the type, the field names aren't used: the other
-- side of `==` or of `++` says it. `Hidden.Cell` isn't in scope by its short
-- name, so the field names alone would say `Cell`, and these would fail.
type Hidden.Cell = { value: Nat }

type Cell = { value: Nat }

def hidden (n: Nat): Option Hidden.Cell := Some ({ value = n })

def one: Nat := 1

test "the other side says" := hidden 1 == Some ({ value = one })

test "appended" := [{ value = 2 }] ++ [({ value = 3 }: Hidden.Cell)] == [{ value = 2 }, { value = 3 }]
