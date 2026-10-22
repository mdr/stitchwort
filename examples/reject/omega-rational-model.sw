-- expect-error: E-OMEGA
-- The facts have a solution over the rationals, so `omega` cannot refute them.
import Std (Nat, Void)

theorem shifted (x: Nat) (y: Nat) (z: Nat) (h1: 1 + 5 * z <= 2 * x + 3 * y) (h2: 2 * x + 3 * y <= 4 + 5 * z)
    (h3: 2 * y + z <= 3 * x + 1) (h4: 3 * x <= 2 * y + z + 2): Void := omega
