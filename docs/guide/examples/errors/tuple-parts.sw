import Std (byDecision)

theorem squareRoot: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, rfl, rfl)
