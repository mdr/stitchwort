-- expect-error: E-EXPORT
-- A function hidden inside a data type, inside another, still can't cross
-- the boundary, and the error says where it is.
type Holder: Type =
  | MkHolder (f: Nat -> Nat)

type Outer: Type =
  | MkOuter (inner: Maybe Holder)

export def useOuter (o: Outer): Nat := 0
