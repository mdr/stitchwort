import Std (byDecision)

-- A proof of "there is an `n` such that ... and ..." is a tuple: the
-- witness, then a proof of each part, in the order the statement says them.
theorem squareRoot: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, rfl)

-- The same tuple as a pattern takes such a proof apart. `_` skips a part.
theorem rootOf ∀ (h: ∃ (n: Nat) => n > 2 ∧ n * n = 49): ∃ (m: Nat) => m * m = 49 :=
  let (n, _, square) := h
  (n, square)

-- Patterns work in arms and lambdas too.
theorem swapAnd ∀ (p q: Prop): p ∧ q → q ∧ p
  | (a, b) => (b, a)

-- One side of a `∧` is `.left` or `.right`.
theorem secondOf ∀ (p q: Prop) (h: p ∧ q): q := h.right
