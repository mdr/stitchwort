-- expect-error: E-TYPE-MISMATCH
-- A vector's length is `double 2`, which is opaque here, so it isn't `4`:
-- the error names `double` and the two ways to use its body.
-- (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat, Vec)

opaque def double (n: Nat): Nat := n + n

def fourOf (xs: Vec Nat (double 2)): Vec Nat 4 := xs
