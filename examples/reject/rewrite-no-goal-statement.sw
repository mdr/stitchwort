-- expect-error: E-REWRITE-NO-GOAL
-- A `rewrite` on a line of its own above the block's result is a statement with no goal; chain the result: `rewrite h then byComputing`.
theorem bad (a: Nat) (b: Nat) (h: a = b): a + 1 = b + 1 :=
  rewrite h
  byComputing
