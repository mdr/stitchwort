-- expect-error: E-UNKNOWN-FIELD
-- `xs`'s type mentions `len`, which only `A` has.

import Std (Vec)

type T =
  | A (len: Nat) (n: Nat) (xs: Vec Nat len)
  | B (n: Nat) (xs: Vec Nat n)

def xsOf (t: T): Nat := t.xs.length
