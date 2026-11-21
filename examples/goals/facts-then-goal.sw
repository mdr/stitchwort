-- `byFacts then ?` shows each part of the goal the facts didn't close as a
-- goal of its own, with the parts they did closed.

theorem partly ∀ (a b c: Prop) (x: a) (f: a → b): b ∧ c := byFacts then ?
