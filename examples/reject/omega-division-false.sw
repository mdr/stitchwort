-- expect-error: E-OMEGA
-- A false goal about a division (`n = 0` breaks it): the message shows
-- `n / 2`, not the function it computes to.
import Std (Nat)

theorem halfLess (n: Nat): n / 2 < n := omega
