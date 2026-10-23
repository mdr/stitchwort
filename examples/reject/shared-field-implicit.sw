-- expect-error: E-UNKNOWN-FIELD
-- `n` is in every constructor but implicit in `VCons2`, so it isn't shared.

type Vec2: Nat -> Type =
  | VNil2 (n: Nat): Vec2 0
  | VCons2 [n: Nat] (head: Nat) (tail: Vec2 n): Vec2 (Succ n)

def nOf (v: Vec2 0): Nat := v.n
