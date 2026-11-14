-- expect-error: E-TYPE-MISMATCH
-- The branches of an untyped `let`'s `if` prove different propositions: the
-- second is checked against the first's, not reported as a universe error.

theorem choose ∀ (c: Bool) (p: 1 = 1) (q: 2 = 2): 1 = 1 :=
  let w := if c then p else q
  p
