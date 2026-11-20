-- `cases` closes a conjunction whose parts each close by computing, by a
-- hypothesis or a part of one, or as such a conjunction in turn, as the pair
-- of their proofs, before it splits anything (SW-4472; docs/syntax.md,
-- "cases"). A goal already proved doesn't wait for a split or a decision.
import Std (Nat)

theorem known ∀ (p: Nat → Prop) (n: Nat) (holds: p n): p n ∧ (1 + 1 == 2) = True ∧ n + 0 = n := cases

theorem fromParts ∀ (p q: Nat → Prop) (n: Nat) (both: p n ∧ q n): q n ∧ p n := cases
