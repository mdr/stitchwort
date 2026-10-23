-- expect-error: E-TYPE-MISMATCH
-- A decimal literal makes the group a `Float`, so a `Nat` operand mismatches
-- under `*` too; `Float.ofNat n` converts it.
import Std (Float)

def scaled (n: Nat): Float := 1.5 * n
