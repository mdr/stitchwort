-- expect-error: E-CASES
-- expect-warning: W-ARROW-FORALL
-- The after-colon form is kept on purpose to test binder introduction.
-- A case still open after a fallback split: the case's path marks the
-- fallback split, and the last note says which variables were split though
-- the goal wasn't stuck on them.
import Std (Bool)

theorem badFallback: (a: Bool) → (b: Bool) → (a ∧ b) = a := cases
