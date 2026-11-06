-- expect-error: E-OMEGA
-- `|x| = x` only for `x` that isn't negative: in the case `x < 0` of
-- `Int.natAbsDichotomy x`, `x = -1` is a counterexample.
import Std (Nat, Int)

theorem absSelf (x: Int): Nat.toInt x.natAbs = x := omega
