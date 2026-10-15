-- expect-error: E-MUTUAL-CONSTRUCTOR
-- A field can mention its data type, but not its constructors: they don't
-- exist until the fields are finished.
type T : Type =
  | A
  | B (p : A = A)
