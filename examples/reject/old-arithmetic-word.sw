-- expect-error: E-UNKNOWN-NAME
-- `omega` was renamed `arithmetic` (D3650); the old name, and other
-- systems' words for it (`lia`, `linarith`), get a note naming ours.
import Std (Nat)

theorem below (n: Nat) (h: n < 3): n <= 5 := omega
