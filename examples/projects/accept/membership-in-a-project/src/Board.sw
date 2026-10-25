-- Membership on numbers and on a record with a derived `DecEq`, where a
-- `Bool` is expected and with `if h:`.
namespace Board

type Position = { row: Nat, column: Nat }

def seen (target: Nat) (visited: List Nat): Bool := target ∈ visited

def hasPotion (target: Position) (potions: List Position): Bool := target ∈ potions

def unvisited (visited: List Position) (cells: List Position): List Position :=
  cells.filter (cell => cell ∉ visited)

def countIfIn (target: Position) (potions: List Position): Nat :=
  if found: target ∈ potions then 1 else 0

test "numbers" := seen 2 [1, 2, 3] && !seen 4 [1, 2, 3]

test "records" :=
  hasPotion { row = 1, column = 2 } [{ row = 0, column = 0 }, { row = 1, column = 2 }]
    && !hasPotion { row = 2, column = 1 } [{ row = 1, column = 2 }]

test "not in" := unvisited [{ row = 0, column = 0 }] [{ row = 0, column = 0 }, { row = 0, column = 1 }] == [{ row = 0, column = 1 }]

test "if h:" := countIfIn { row = 3, column = 4 } [{ row = 3, column = 4 }] == 1
