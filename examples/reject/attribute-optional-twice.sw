-- expect-error: E-ATTRIBUTE
type Shape =
  | Circle (radius: Nat) (@[js.optional, js.optional] fill: Option Text)
