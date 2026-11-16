-- expect-error: E-TYPE-MISMATCH
-- A comparison in the statement is shown as it is written, `3 < n`, not as
-- what `<` computes to, `4 ≤ n` (SW-3100).
import Std (Bool)

theorem bad ∀ (n: Nat) (h: True): 3 < n := h
