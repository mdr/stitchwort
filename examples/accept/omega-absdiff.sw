-- `omega` with `Nat.absDiff`: it computes to `(a - b) + (b - a)`, two
-- subtractions with their cases, so a distance needs no unfolding by hand,
-- in a fact, in the goal, or inside a definition that uses it.

import Std (Nat)

theorem fromFact ∀ (a b: Nat) (h: Nat.absDiff a b ≤ 3): a ≤ b + 3 := omega

theorem toGoal ∀ (a b k: Nat) (low: a ≤ b + k) (high: b ≤ a + k): Nat.absDiff a b ≤ k := omega

theorem symmetric ∀ (a b: Nat): Nat.absDiff a b = Nat.absDiff b a := omega

theorem triangle ∀ (a b c: Nat): Nat.absDiff a c ≤ Nat.absDiff a b + Nat.absDiff b c := omega

-- The Manhattan distance, through a definition.
type Position = { row: Nat, column: Nat }

def Position.distance (position other: Position): Nat :=
  Nat.absDiff position.row other.row + Nat.absDiff position.column other.column

theorem rowNear ∀ (position other: Position) (length: Nat)
    (near: position.distance other ≤ length):
    other.row ≤ position.row + length ∧ position.row - length ≤ other.row :=
  Both (omega [near]) (omega [near])
