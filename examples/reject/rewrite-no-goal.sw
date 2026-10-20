-- expect-error: E-REWRITE-NO-GOAL
-- `let` without a type gives `rewrite` no goal to look in. Ascribe it: `(rewrite … in …: a = b)`.
theorem bad (a: Nat) (b: Nat) (h: a = b): a + 1 = b + 1 :=
  let p := rewrite h
  p
