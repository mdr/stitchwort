-- expect-error: E-CASES
-- Of the propositions, only an `∨` can be named: a conjunction has one case,
-- and its sides are taken apart by the closers anyway.
import Std (Bool)

theorem leftOf ∀ (a b: Bool) (h: (a ∧ b) = True ∧ a = True): a = True := cases h then byComputing
