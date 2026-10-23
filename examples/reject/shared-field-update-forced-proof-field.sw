-- expect-error: E-RECORD-UPDATE
-- The proof `ok` mentions `n` and `xs`, so it must be updated too.
import Std (Vec)

type Sized =
  | A (n: Nat) (xs: Vec Nat n) (ok: xs = xs)
  | B (n: Nat) (xs: Vec Nat n) (ok: xs = xs)

def f (a: Sized): Sized := { a | n = 1, xs = VCons 7 VNil }
