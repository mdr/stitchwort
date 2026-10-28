-- expect-error: E-DUPLICATE
-- A data type declared twice, with an instance on it ahead of both.
instance Foo.i: Foo T :=
  { x = A }
type T = | A
type T = | B
interface Foo (a: Type) =
  { x: a }
