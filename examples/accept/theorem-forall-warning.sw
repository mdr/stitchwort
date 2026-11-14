-- expect-warning: W-THEOREM-FORALL
-- A theorem whose statement starts with `∀` warns (W-THEOREM-FORALL, D3470):
-- its variables belong before the colon, `theorem addZero (n: Nat): n + 0 = n`,
-- the same statement with the same hash. The editor's quick fix "Move ∀
-- variables before the colon" makes the edit; `stitchwort sweep
-- theorem-binders` makes it across a folder. The warning doesn't stop the
-- file being accepted.
--
-- A `∀` after a premise, `n < 3 → ∀ (k: Nat) => …`, is left alone: moving `k`
-- would change the statement.
theorem addZero: ∀ (n: Nat) => n + 0 = n
  | Zero => rfl
  | Succ k => rfl

theorem addZeroBefore ∀ (n: Nat): n + 0 = n := match n with
  | Zero => rfl
  | Succ k => rfl

theorem afterPremise ∀ (n: Nat): n < 3 → ∀ (k: Nat) => k + 0 = k := h k => rfl
