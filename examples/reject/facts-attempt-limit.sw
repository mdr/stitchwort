-- expect-error: E-FACTS
-- `step` fits with any three of the eight `one` facts, 512 ways, and `q x y z`
-- holds for none: the search stops at its limit of attempts, and says so.

theorem tooMany ∀ (q: Nat → Nat → Nat → Prop) (r: Prop) (one: Nat → Prop)
    (step: ∀ (x y z: Nat) => one x → one y → one z → q x y z → r) (h0: one 0) (h1: one 1) (h2: one 2) (h3: one 3)
    (h4: one 4) (h5: one 5) (h6: one 6) (h7: one 7):
    r :=
  byFacts

-- Seven facts that each prove `g x` from `g x`: a premise that is the part
-- being proved is never tried, so this fails at once.
theorem looping ∀ (g: Nat → Prop) (s1 s2 s3 s4 s5 s6 s7: ∀ (x: Nat) => g x → g x): g 3 := byFacts
