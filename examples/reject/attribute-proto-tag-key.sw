-- expect-error: E-ATTRIBUTE
@[js.tag "__proto__"]
type Shape =
  | Circle (radius: Nat)
