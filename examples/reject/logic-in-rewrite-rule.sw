-- expect-error: E-PARSE
-- A bare `in` ends a `rewrite` rule, so `rewrite h (3 in xs) in rfl` needs its
-- brackets: without them the rule is `h 3` and the body `xs in rfl`
-- (D1201). accept/rewrite.sw has the bracketed form.
theorem same (f: Prop -> Nat) (g: Prop -> Nat) (xs: List Nat) (h: (p: Prop) -> f p = g p): f (3 in xs) = g (3 in xs) :=
  rewrite h 3 in xs in rfl
