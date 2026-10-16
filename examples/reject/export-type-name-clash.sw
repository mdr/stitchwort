-- expect-error: E-EXPORT
-- Two different types would both be called `Shape` in the TypeScript
-- declarations.
type Flat.Shape : Type =
  | Square (side : Nat)

type Solid.Shape : Type =
  | Cube (side : Nat)

export
volume : Solid.Shape -> Flat.Shape -> Nat
volume (Solid.Shape.Cube s) (Flat.Shape.Square t) = s * s * s + t
