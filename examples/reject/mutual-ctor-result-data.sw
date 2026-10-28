-- expect-error: E-MUTUAL-PARAMETERS
-- A constructor's result type names a later data type, which names the
-- first back: they're defined together, so they need the same parameters.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a Zero
  | VCons (x: a) (xs: Vec a n): Box a (Succ n)

type Box: Type 1 =
  | Mk [a: Type] (xs: List a) (rest: Vec)
