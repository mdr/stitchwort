-- expect-error: E-EXPORT
-- ...also in a record field: decoding `rows` would have to check every
-- row's length.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

type Grid = { height: Nat, width: Nat, rows: Vec (Vec Bool width) height }

export def flip (g: Grid): Grid := g
