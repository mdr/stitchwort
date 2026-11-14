-- expect-error: E-TYPE-MISMATCH
-- A proof of a whole conjunction doesn't build a test fact of `&&`: its
-- reading is `xs.contains x = True ∧ x < 3 = True`, not `k`'s type. The note
-- says to build it part by part with `Both`.
import Std (Bool, List, Nat)

theorem whole ∀ (x: Nat) (xs: List Nat) (k: x ∈ xs ∧ x < 3): (xs.contains x && x < 3) = True := k
