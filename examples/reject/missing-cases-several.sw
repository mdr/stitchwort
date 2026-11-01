-- expect-error: E-NONEXHAUSTIVE
-- Every missing case is listed, as an arm to paste (SW-1027): `Square` and
-- `Tri` both, not only the first.
type Shape =
  | Circle (r: Nat)
  | Square (s: Nat)
  | Tri (a: Nat) (b: Nat)

def size: Shape → Nat
  | Circle r => r
