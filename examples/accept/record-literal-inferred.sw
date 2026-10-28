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
