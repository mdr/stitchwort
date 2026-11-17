-- A rewrite keeps a sum's written form on both sides of its step (SW-2924):
-- `f (a + 1)` before and `f (b + 1)` after, not `f (Succ b)`.
def f (n: Nat): Nat := n * 2

theorem rewriteSteps ∀ (a b: Nat) (same: a = b): f (a + 1) = f (b + 1) := rewrite same then ?
