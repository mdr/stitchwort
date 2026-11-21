-- expect-error: E-FACTS
-- No witness is invented: nothing in scope says `q n` of any `n`.

theorem noWitness ∀ (p q: Nat → Prop) (h: p 3): ∃ (n: Nat) => q n := byFacts
