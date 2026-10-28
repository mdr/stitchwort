-- expect-error: E-OMEGA
-- `a <= 3 || 5 <= a` is false for `a = 4`: by cases on `a <= 3`, the case
-- where it's false leaves `5 <= a`, which `omega` can't prove.
import Std (Nat)

theorem gap (a: Nat): (a <= 3 || 5 <= a) = True := omega
