-- expect-error: E-ATTRIBUTE
type Shape =
  | @[js.tag "type"] Circle (radius: Nat)
