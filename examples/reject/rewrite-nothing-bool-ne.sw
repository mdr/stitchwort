-- expect-error: E-REWRITE-NOTHING
-- A `Bool` `!=` beside `=` in a statement is the proposition `≠`, so the goal
-- holds no `Bool` `a != b` for the rewrite to find.
def neRewrite (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a != b) = (b != a) :=
  rewrite h in rfl
