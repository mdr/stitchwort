-- `cases` closes a goal that is a record of proofs by its fields, as it
-- closes a conjunction by its parts (SW-4485; docs/syntax.md, "cases"): each
-- field closes by computing, by a hypothesis or a part of one, or is such a
-- record or conjunction in turn.
import Std (Nat)

type Between (low n high: Nat): Prop = { above: low ≤ n, below: n ≤ high }

theorem betweenOf ∀ (low n high: Nat) (inside: (low <= n && n <= high) = True): Between low n high := cases

theorem betweenAndMore ∀ (low n high: Nat) (above: low ≤ n) (below: n ≤ high): Between low n high ∧ n + 0 = n := cases
