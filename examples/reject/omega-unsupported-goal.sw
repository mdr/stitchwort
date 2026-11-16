-- expect-error: E-ARITHMETIC
-- `arithmetic` only proves arithmetic goals; an equation between lists is not one.
import Std (Nat, List)

theorem notArith (xs: List Nat): xs = xs := arithmetic
