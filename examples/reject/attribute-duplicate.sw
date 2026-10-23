-- expect-error: E-ATTRIBUTE
type Shape =
  | @[js.name "CIRCLE"] @[js.name "ROUND"] Circle (radius: Nat)
