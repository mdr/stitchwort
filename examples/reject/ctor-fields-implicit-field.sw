-- expect-error: E-UNKNOWN-FIELD
-- Braces name explicit fields only; an implicit field is matched
-- positionally, `VCons [n := k] …`.

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (head: a) (tail: Vec a n): Vec a (Succ n)

def lengthOf (xs: Vec a m): Nat := match xs with
  | VNil            => 0
  | VCons { n, .. } => Succ n
