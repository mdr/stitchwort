-- A `match` on a `Vec` at `Succ n` needs only the `VCons` arm: `VNil` can't
-- be here. Finding that out must not need the library's `Fin` constructors,
-- which a program that never mentions `Fin` hasn't loaded.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def head (items: Vec Nat (Succ n)): Nat :=
  match items with
    | VCons x _ => x
