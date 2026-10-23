-- expect-error: E-RECORD-UPDATE
-- Constructor `OA` has its own field `v` mentioning `n`.
import Std (Vec)

type Own =
  | OA (n: Nat) (v: Vec Nat n)
  | OB (n: Nat)

def f (a: Own): Own := { a | n = 1 }
