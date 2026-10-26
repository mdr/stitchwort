-- expect-error: E-INDEX-STUCK
-- The vector's length is `succ n`, which is opaque, so whether `VNil` (length
-- 0) can be here can't be decided from `succ n = 0`: the error names `succ`.
-- (docs/proposals/opaque-definitions.md §6.10.)
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

opaque def succ (n: Nat): Nat := Succ n

def size: Vec a (succ n) → Nat
  | VNil      => 0
  | VCons _ _ => 1
