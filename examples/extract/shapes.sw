-- User-defined data types cross the JS boundary as tagged objects:
-- `{ tag: "Rect", width: 2n, height: 5n }`.
--
-- run: area (Square 3)
-- run: area (Rect 2 5)
-- run: areas [Square 1, Rect 2 3]
-- run: grow (Rect 2 5)

type Shape: Type =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

export def area: Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h

export def areas: List Shape -> List Nat
  | Nil         => Nil
  | Cons s rest => Cons (area s) (areas rest)

export def grow: Shape -> Shape
  | Square s => Square (Succ s)
  | Rect w h => Rect (Succ w) (Succ h)
