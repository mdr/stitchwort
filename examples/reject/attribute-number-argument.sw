-- expect-error: E-PARSE
-- An attribute's argument is a string.
type Shape =
  | @[js.name 123] Circle (radius: Nat)
