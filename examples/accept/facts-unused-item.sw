-- expect-warning: W-FACTS-UNUSED
-- A listed term no part of the goal used is warned about at the term, so a
-- list doesn't only grow.

theorem lessTrans ∀ (a b c: Nat) (ab: a < b) (bc: b < c): a < c := arithmetic

theorem leftPart ∀ (a b: Prop) (h: a ∧ b): a := byFacts [lessTrans]
