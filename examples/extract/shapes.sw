-- User-defined data types cross the JS boundary as tagged objects:
-- `{ tag: "Rect", width: 2n, height: 5n }`.
--
-- run: area (Square 3)
-- run: area (Rect 2 5)
-- run: areas [Square 1, Rect 2 3]
-- run: grow (Rect 2 5)

type Shape : Type =
  | Square (side : Nat)
  | Rect (width : Nat) (height : Nat)

mul : Nat -> Nat -> Nat
mul Zero     n = 0
mul (Succ m) n = n + mul m n

export
area : Shape -> Nat
area (Square s) = mul s s
area (Rect w h) = mul w h

export
areas : List Shape -> List Nat
areas Nil           = Nil
areas (Cons s rest) = Cons (area s) (areas rest)

export
grow : Shape -> Shape
grow (Square s) = Square (Succ s)
grow (Rect w h) = Rect (Succ w) (Succ h)
