-- expect-error: E-FACTS
-- Seven facts that each prove `g x` from `g x` give the search seven ways at
-- every depth and nothing to end on: it stops at its limit of attempts,
-- and says so.

theorem looping ∀ (g: Nat → Prop) (s1 s2 s3 s4 s5 s6 s7: ∀ (x: Nat) => g x → g x): g 3 := byFacts
