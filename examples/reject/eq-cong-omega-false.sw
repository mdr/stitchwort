-- expect-error: E-ARITHMETIC
-- `Eq.cong Some (arithmetic)` against a false `Some a = Some b`: `arithmetic` is
-- blamed for `a = b`, the goal the expected type gives it.
import Std (Nat, Option, Eq)

theorem shifted (n: Nat): Some (n + 1) = Some (n + 2) :=
  Eq.cong Some (arithmetic)
