-- expect-error: E-NONEXHAUSTIVE
-- A `match` on a `Vec` whose length is 2^128, missing `VCons`. Telling
-- whether `VNil` can be its tail means comparing 2^128 with 2^128 - 1: the
-- `Succ`s both share are taken off at once, not one at a time, which used
-- 10 GB within seconds (SW-2580).
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 340282366920938463463374607431768211456
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head (items: Vec Nat 340282366920938463463374607431768211456): Nat :=
  match items with
    | VNil => 0
