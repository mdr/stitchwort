-- expect-error: E-PARSE
-- There is no `deriving`: a declared type gets `DecEq`, `Ord`, `Show` and
-- `Finite` derived when it is declared.
type Colour = | Red | Green | Blue
  deriving DecEq
