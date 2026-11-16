-- expect-error: E-ALGEBRA
-- The sides differ by `b`: the message shows both normal forms and the difference.
import Std (Nat)

theorem extra (b: Nat) (m: Nat) (p: Nat): b * m * p + b = b * m * p + 2 * b := algebra
