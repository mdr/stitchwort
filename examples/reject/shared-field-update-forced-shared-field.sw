-- expect-error: E-RECORD-UPDATE
-- Updating `n` needs `xs` updated too, since its type mentions `n`.
import Std (Vec)

type Sized =
  | A (n: Nat) (xs: Vec Nat n)
  | B (n: Nat) (xs: Vec Nat n)

def f (a: Sized): Sized := { a | n = 1 }
