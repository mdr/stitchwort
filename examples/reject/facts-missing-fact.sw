-- expect-error: E-FACTS
-- `f` would give `c` from `a`, but nothing in scope is `a`: the part left
-- open is shown with the facts whose conclusions come nearest.

theorem missing ∀ (a b c: Prop) (f: a → c) (y: b): c ∧ b := byFacts
