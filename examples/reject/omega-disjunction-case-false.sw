-- expect-error: E-OMEGA
-- `omega` splits `h` into its cases; in the case `a = 5` the goal is false,
-- and the message names that case.
import Std (Nat, Or)

theorem caseFalse (a: Nat) (h: Or (a = 1) (a = 5)): a <= 2 := omega
