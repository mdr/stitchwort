-- expect-error: E-TERMINATION
-- No decrease is read from an index equation (D143): in the `VCons` branch
-- `m` is one less than `n`, but `replicate m 0` isn't part of `v`, so the
-- call isn't smaller. Pairs with `toList` in accept/indexed-families.sw,
-- which recurses on the field `xs` (docs/proposals/indexed-families.md §6.7,
-- test 13).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def replicate: (n: Nat) → a → Vec a n
  | Zero, _   => VNil
  | Succ k, x => VCons x (replicate k x)

def down [n: Nat]: Vec Nat n → Nat
  | VNil                 => 0
  | VCons [n := m] _ _   => down [n := m] (replicate m 0)
