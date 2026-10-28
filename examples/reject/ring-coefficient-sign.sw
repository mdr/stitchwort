-- expect-error: E-RING
-- With a `-` written, the hypothesis is used only as written.
import Std (Int)

theorem wrongSign (a: Int) (b: Int) (h: a = b): a - b = 0 := ring [-h]
