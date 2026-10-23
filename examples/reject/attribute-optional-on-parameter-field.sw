-- expect-error: E-ATTRIBUTE
-- A field whose type is a parameter isn't written as an `Option`, even when
-- the parameter is one somewhere.
type Box (a: Type) =
  | Full (@[js.optional] value: a)
