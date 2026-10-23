-- expect-error: E-PARSE
type Shape =
  | @[js.name "CIRCLE" "ROUND"] Circle (radius: Nat)
