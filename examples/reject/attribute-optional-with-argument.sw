-- expect-error: E-ATTRIBUTE
type Shape =
  | Circle (radius: Nat) (@[js.optional "yes"] fill: Option Text)
