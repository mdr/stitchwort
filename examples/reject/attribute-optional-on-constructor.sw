-- expect-error: E-ATTRIBUTE
type Shape =
  | @[js.optional] Circle (radius: Nat) (fill: Option Text)
