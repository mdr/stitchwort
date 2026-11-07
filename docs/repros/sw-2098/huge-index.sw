-- Fuzz case 1834 (seed 0x5eede1ab00000685, Overmind, f06dd23cd), mutated from
-- examples/reject/index-missing-arm.sw: still running after 60 s. The index is
-- 2^128.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 340282366920938463463374607431768211456
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def zipWith (f: a → b → c): Vec a n → Vec b n → Vec c n
  | VNil, VNil => VNil
