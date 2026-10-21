-- A walk on a grid. Coordinates are `Int`, so the walk can go below zero:
-- south and west decrease a coordinate, and the origin is in the middle.

import Std (Int)

type Move = | North | South | East | West

type Point = { x: Int, y: Int }

def origin: Point := { x = 0, y = 0 }

def move (p: Point): Move -> Point
  | North => { p | y = p.y + 1 }
  | South => { p | y = p.y - 1 }
  | East  => { p | x = p.x + 1 }
  | West  => { p | x = p.x - 1 }

def walk (p: Point) (ms: List Move): Point := ms.foldLeft move p

-- Manhattan distance from the origin: `Int.natAbs` drops the sign.
def distance (p: Point): Nat := Int.natAbs p.x + Int.natAbs p.y

def sample: List Move := [West, West, South, South, South, East, North, West]

test "sample ends at (-2, -2)" := walk origin sample == { x = -2, y = -2 }
test "sample is 4 away" := distance (walk origin sample) == 4
test "going back returns to the origin" := walk origin [South, West, North, East] == origin

theorem westOfOrigin: (move origin West).x = -1 := rfl

theorem southOfOrigin: (move origin South).y = -1 := rfl

theorem farCorner: distance { x = -3, y = 4 } = 7 := rfl

-- A torus: a 10 by 5 board where walking off one edge comes back on the
-- opposite one. The board is `Nat` coordinates with their bounds as proofs.
type Cell = { col: Nat, row: Nat, colOk: col < 10, rowOk: row < 5 }

def cell (p: Point): Cell := { col = Int.modNat p.x 10, row = Int.modNat p.y 5, colOk = Int.modNatLt p.x 10, rowOk = Int.modNatLt p.y 5 }

test "(-2, -2) is column 8" := (cell (walk origin sample)).col == 8
test "(-2, -2) is row 3" := (cell (walk origin sample)).row == 3
test "(10, 5) is the corner cell" := (cell { x = 10, y = 5 }).col == 0
test "(-1, -1) is the far corner" := (cell { x = -1, y = -1 }).row == 4

-- The same remainder as an `Int`, for the Euclidean `%`: never negative,
-- and below the size of the board.
theorem colNonneg (x: Int): 0 <= x % 10 := Int.modNonneg x 10

theorem colSmall (x: Int): x % 10 < 10 := Int.modLtAbs x 10
