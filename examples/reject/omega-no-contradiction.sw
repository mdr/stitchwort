-- expect-error: E-OMEGA
-- A goal that isn't arithmetic is proved only when the facts contradict each
-- other; `n < 5` doesn't.
import Std (Nat, List)

theorem notArith (xs: List Nat) (n: Nat) (h: n < 5): xs = Nil := omega
