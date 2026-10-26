-- expect-error: E-TYPE-MISMATCH
-- A number pattern tests the value: in the second equation all that's known
-- about `x` is its sign, and that its size isn't 0 when it's `OfNat`, not
-- that the size is a `Succ`, so `R x` doesn't compute to `Bool`. Match
-- `OfNat Zero` and the other constructors instead (see
-- accept/int-patterns.sw).
def R: Int → Type
  | OfNat Zero => Nat
  | _ => Bool

def make: (x: Int) → R x
  | 0 => 0
  | x => False
