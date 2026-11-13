-- A case no arm covers is fine when a variable in scope that isn't matched
-- has an indexed family's type that no constructor fits once the matches
-- have refined it (D3534, D3535): `i: Fin 0` has no values.

import Std (Nat)

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

-- Numbers below `n`.
type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

-- `VNil` is left out: `i` would be a `Fin 0`. Only `v` is matched.
def first (v: Vec a n) (i: Fin n): a := match v with
  | VCons x _ => x

-- As arms.
def get: (v: Vec a n) -> Fin n -> a
  | VCons x _, FZero => x
  | VCons _ xs, FSucc j => get xs j

test "get" := get (VCons 5 (VCons 6 VNil)) (FSucc FZero) == 6
