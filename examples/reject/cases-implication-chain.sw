-- expect-error: E-CASES
-- `cases` applies each implication once, to premises in scope; it never
-- chains: `b`, added from `f` and `x`, isn't a premise for `g`.
theorem chain ∀ (a b c: Prop) (f: a → b) (g: b → c) (x: a): c := cases
