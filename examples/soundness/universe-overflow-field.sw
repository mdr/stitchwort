-- expect-error: E-PARSE
-- SW-902: with the step wrapped, `Type 4294967295` was in `Type 0`, so it fit
-- as a field of a type in `Type 0`.
type Box: Type 0 =
  | MkBox (t: Type 4294967295)
