-- expect-error: E-CASES
-- A case still open after `cases` introduced a goal's binders: the case
-- and its hypotheses are shown under their written names, and an unnamed
-- hypothesis (`A → B`) by its position.
import Std (Bool, Nat)

theorem badAfter ∀ (a: Bool) (b: Bool): (a ∧ b) = a := cases

theorem badUnnamed ∀ (n: Nat): n = 3 → n = 4 := cases
