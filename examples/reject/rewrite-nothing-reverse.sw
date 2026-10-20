-- expect-error: E-REWRITE-NOTHING
-- `<-` looks for the right side, `b`. The goal only has `a`.
theorem bad (a: Nat) (b: Nat) (h: a = b): Succ a = Succ a :=
  rewrite <- h
