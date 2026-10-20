-- An indexed family used only inside an export is fine: the boundary types
-- are `List Nat` and `Nat`. Its forced field `n` is stored and its impossible
-- branches generate no code (paired with reject/export-indexed-*.sw).
--
-- run: firstOr 7 []
-- run: firstOr 7 [3, 4]
-- run: sumPairs [1, 2, 3]
-- run: sumPairs []
type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def fromList: (xs: List a) -> Vec a (List.length xs)
  | Nil       => VNil
  | Cons x xs => VCons x (fromList xs)

def head: Vec a (Succ n) -> a
  | VCons x _ => x

def zipWith (f: a -> b -> c): Vec a n -> Vec b n -> Vec c n
  | VNil, VNil             => VNil
  | VCons x xs, VCons y ys => VCons (f x y) (zipWith f xs ys)

def toList: Vec a n -> List a
  | VNil       => Nil
  | VCons x xs => Cons x (toList xs)

export def firstOr (default: Nat): List Nat -> Nat
  | Nil       => default
  | Cons x xs => head (fromList (Cons x xs))

-- Adds each element to itself, through two vectors of one length.
export def sumPairs (xs: List Nat): Nat :=
  List.sum (toList (zipWith (a b => a + b) (fromList xs) (fromList xs)))
