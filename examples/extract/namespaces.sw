-- Exports in namespaces (docs/proposals/namespaces.md §7.3). An export is
-- imported in JS by its short name: `Geometry.Shape.area` is `area`, and the
-- type `Geometry.Shape` is `Shape` in the TypeScript declarations. Two
-- exports that both use `Shape` reach the same type, which is fine. Run lines
-- are Stitchwort, so they use the full name.
--
-- run: Geometry.Shape.area (Geometry.Shape.Square 3)
-- run: Geometry.Shape.area (Geometry.Shape.Rect 2 5)
-- run: grow (Geometry.Shape.Square 1)

type Geometry.Shape : Type =
  | Square (side : Nat)
  | Rect (width : Nat) (height : Nat)

export def Geometry.Shape.area : Geometry.Shape -> Nat
  | Geometry.Shape.Square s => s * s
  | Geometry.Shape.Rect w h => w * h

export def grow : Geometry.Shape -> Geometry.Shape
  | Geometry.Shape.Square s => Geometry.Shape.Square (s + 1)
  | Geometry.Shape.Rect w h => Geometry.Shape.Rect (w + 1) (h + 1)
