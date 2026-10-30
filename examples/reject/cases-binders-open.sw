-- expect-error: E-CASES
-- A case still open after `cases` introduced the goal's binders: the case
-- and its hypotheses are shown under the names written after the colon, and
-- an unnamed hypothesis (`A → B`) by its position.
import Std (Bool, Nat)

theorem badAfter: (a: Bool) → (b: Bool) → (a ∧ b) = a := cases

theorem badUnnamed: (n: Nat) → (n = 3) → n = 4 := cases
