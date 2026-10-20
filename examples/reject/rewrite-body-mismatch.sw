-- expect-error: E-TYPE-MISMATCH
-- The body is checked against the goal after the rewrite, `b + 1 = b`, not the original.
theorem bad (a: Nat) (b: Nat) (h: a = b) (p: a + 1 = b): a + 1 = b :=
  rewrite h in p
