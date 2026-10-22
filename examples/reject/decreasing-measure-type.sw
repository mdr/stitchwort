-- expect-error: E-TYPE-MISMATCH
-- The measure is a `Nat`.
import Std (List, Nat)

def size (xs: List Nat): Nat
  decreasing xs
:=
  match xs with
    | Nil => 0
    | Cons x rest => 1 + size rest
