-- expect-error: E-PARSE
-- `at` after a rule starts the hypothesis to rewrite, so a hypothesis
-- called `at` can't be an argument of the rule.
import Std (Nat)

theorem flipped (n: Nat) (m: Nat) (at: n = m): m = n :=
  rewrite Eq.symm at in rfl
