-- expect-error: E-ARITHMETIC
-- `x / 3 * 3` rounds down: `x = 1` breaks it. The message shows `x / 3` and
-- `x % 3` with what `arithmetic` knows about them.
import Std (Int)

theorem divMulBack (x: Int): x / 3 * 3 = x := arithmetic
