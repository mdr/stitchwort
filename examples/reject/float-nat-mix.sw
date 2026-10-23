-- expect-error: E-TYPE-MISMATCH
-- A decimal literal makes the group a `Float`, so a `Nat` operand mismatches.
import Std (Float)

def scaled (n: Nat): Float := 1.5 + n
