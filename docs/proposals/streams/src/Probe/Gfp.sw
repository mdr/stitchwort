namespace Probe.Gfp

-- The greatest predicate `r` with `r x → f r x`, for a rule `f` (Knaster-Tarski).
def Gfp (f: (a → Prop) → a → Prop) (x: a): Prop := ∃ (r: a → Prop) => (∀ (y: a) => r y → f r y) ∧ r x

-- Coinduction: to prove `Gfp f x`, give any `r` that holds at `x` and that the rule keeps.
theorem Gfp.coinduct ∀ (f: (a → Prop) → a → Prop) (r: a → Prop) (kept: ∀ (y: a) => r y → f r y) (x: a) (h: r x):
    Gfp f x :=
  Witness r (Both kept h)

-- Unfolding once, for a monotone rule.
theorem Gfp.unfold ∀ (f: (a → Prop) → a → Prop)
    (mono: ∀ (r s: a → Prop) => (∀ (y: a) => r y → s y) → ∀ (y: a) => f r y → f s y) (x: a)
    (h: Gfp f x):
    f (Gfp f) x :=
  match h with | Witness r both => mono r (Gfp f) (y ry => Gfp.coinduct f r both.left y ry) x (both.left x both.right)
