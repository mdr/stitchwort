-- expect-error: E-DUPLICATE
-- The second instance reuses the first one's name, and the interface comes
-- after them, so it shifts down when the duplicate is left out.
instance Foo.i: Foo Nat :=
  { x = 0 }
instance Foo.i: Foo Nat :=
  { x = 0 }
interface Foo (a: Type) =
  { x: a }
