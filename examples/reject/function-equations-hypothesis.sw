-- expect-error: E-CASES
-- `kind.eq2` holds only where arm 1 doesn't: its hypothesis `x1 ≠ 3` must
-- be proved, and `cases` can't prove it of a number it knows nothing about.
import Std (Nat)

def kind: Nat → Nat
  | 3 => 1
  | _ => 0

theorem kindAnything (n: Nat): kind n = 0 := kind.eq2 n cases
