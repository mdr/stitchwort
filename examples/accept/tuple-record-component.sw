-- A tuple checked against a pair type checks each component against its
-- part, so a record literal inside one needs no annotation.

type Position = { row: Nat, column: Nat }

def corner (p: Position): (Nat, Position) := (1, { row = p.row, column = 0 })

def corners (p: Position): List (Nat, Position) := [(1, { row = p.row, column = 0 }), (2, { row = 0, column = p.column })]

test "the corners' second components" := (corners { row = 3, column = 4 }).map (.snd.row) == [3, 0]
