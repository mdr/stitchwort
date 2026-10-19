-- expect-error: E-UNIVERSE
-- A type in `Type` can't contain a `Type` as a field: that's a universe too big.
type Box: Type =
  | MkBox (t: Type)
