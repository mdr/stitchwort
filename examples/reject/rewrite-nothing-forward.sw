-- expect-error: E-REWRITE-NOTHING
-- The rule's left side is `a`, but the goal only has `b`: the other direction needs `<-`.
theorem bad (a: Nat) (b: Nat) (h: a = b): Succ b = Succ b :=
  rewrite h
