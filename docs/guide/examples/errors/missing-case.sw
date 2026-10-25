type Shape =
  | Circle (radius: Nat)
  | Rect (width: Nat) (height: Nat)
  | Dot

def Shape.area: Shape → Nat
  | Circle radius => 3 * radius * radius
  | Rect width height => width * height
