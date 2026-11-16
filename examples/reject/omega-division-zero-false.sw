-- expect-error: E-ARITHMETIC
-- `n / 0` is 0, not `n`: false at `n = 1`.
import Std (Nat)

theorem divZeroSelf (n: Nat): n / 0 = n := arithmetic
