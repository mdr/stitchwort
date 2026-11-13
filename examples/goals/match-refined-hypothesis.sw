-- Matching on a parameter refines the hypotheses about it: in the second
-- branch, `holds` is about `k`, a variable bound after it.
theorem bounded ∀ (p: Nat → Prop) (n: Nat) (holds: p n) (small: ∀ (m: Nat) => p m → m < 3): n < 4 :=
  match n with
    | Zero => rfl
    | Succ k => ?
