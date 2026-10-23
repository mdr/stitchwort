-- expect-error: E-ATTRIBUTE
type Shape =
  | @[js.name] Circle (radius: Nat)
