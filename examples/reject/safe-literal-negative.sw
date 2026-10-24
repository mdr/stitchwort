-- expect-error: E-SAFE-LITERAL
-- A `SafeNat` can't be negative (SW-354): use a `SafeInt`.
import Std (SafeNat)

def below: SafeNat := -1
