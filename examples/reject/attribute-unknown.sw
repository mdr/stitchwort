-- expect-error: E-ATTRIBUTE-UNKNOWN
-- The set of attributes is closed: a misspelt one is an error, never ignored.
type Shape =
  | @[js.rename "CIRCLE"] Circle (radius: Nat)
