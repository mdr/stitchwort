-- expect-error: E-ATTRIBUTE
@[js.optional]
type Shape =
  | Circle (radius: Nat) (fill: Option Text)
