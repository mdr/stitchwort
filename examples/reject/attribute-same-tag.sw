-- expect-error: E-JS-NAME-CLASH
type Shape =
  | @[js.name "ROUND"] Circle (radius: Nat)
  | @[js.name "ROUND"] Ring (inner: Nat) (outer: Nat)
