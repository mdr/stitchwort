-- expect-error: E-REFL
-- Inputs of the program's own data types are enumerated from their
-- constructors, smallest first: `Square 1` is the first shape the statement
-- is false for (acceptance test 4).
type Shape =
  | Circle (radius: Nat)
  | Square (side: Nat)

def size (shape: Shape): Nat :=
  match shape with
    | Circle radius => radius
    | Square side => side

def area (shape: Shape): Nat :=
  match shape with
    | Circle radius => 3 * radius * radius
    | Square side => side * side

theorem areaFormula (shape: Shape): area shape = 3 * size shape * size shape := rfl
