-- expect-error: E-REWRITE-NOTHING
-- The goal is written `≠`, so the `!=` note must not appear (SW-3125).
def neRewrite (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a ≠ b) = (b ≠ a) :=
  rewrite h then byComputing
