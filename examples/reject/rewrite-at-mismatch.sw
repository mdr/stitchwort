-- expect-error: E-TYPE-MISMATCH
-- After the rewrite, `h` is about `b`; the goal is still about `a`.
theorem bad (a: Nat) (b: Nat) (e: a = b) (h: a + 1 = 5): a + 1 = 5 :=
  rewrite e at h
