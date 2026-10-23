-- expect-error: E-UNKNOWN-FIELD
-- Braces give explicit fields only; an implicit field is solved by
-- unification, or given positionally as `VCons [n := k] …`.

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def one: Vec Nat 1 := VCons { n = 0, x = 1, xs = VNil }
