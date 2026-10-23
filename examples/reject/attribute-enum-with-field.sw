-- expect-error: E-ATTRIBUTE
@[js.enum]
type Shape =
  | Dot
  | Circle (radius: Nat)
