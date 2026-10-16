-- expect-error: E-AMBIGUOUS
-- Two types of this file have a constructor `Square`. `Shape.Square` and
-- `Tile.Square` always work; `Square` on its own is ambiguous.
type Shape : Type =
  | Square (side : Nat)

type Tile : Type =
  | Square (colour : Nat)

unit : Shape
unit = Square 1
