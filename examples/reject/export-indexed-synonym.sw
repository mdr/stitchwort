-- expect-error: E-EXPORT
-- ...also through a type synonym.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def Row: Type := Vec Bool 5

export def first: Row → Bool
  | VCons x _ => x
