-- expect-error: E-TYPE-MISMATCH
-- A `decreasing` measure that names a type declared below: it's found (the
-- declaration is checked first), but it isn't a `Nat`.
import Std (Nat)

def count (n: Nat): Nat
    decreasing Stack
:=
  match n with
    | Zero => 0
    | Succ k => count k

type Stack = { size: Nat }
