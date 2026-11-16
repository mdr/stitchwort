-- expect-error: E-PARSE
-- A bare `in` still ends a `rewrite` rule, so that the old spelling
-- `rewrite h in t` gets an error naming `then` (D3648); membership in a rule
-- needs its brackets, `rewrite h (3 in xs) then byComputing`.
-- accept/rewrite.sw has the bracketed form.
theorem same (f: Prop -> Nat) (g: Prop -> Nat) (xs: List Nat) (h: ∀ (p: Prop) => f p = g p): f (3 in xs) = g (3 in xs) :=
  rewrite h 3 in xs then byComputing
