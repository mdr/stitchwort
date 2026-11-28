-- A hypothesis concluding in a bare variable of a `Prop` binder is a fact:
-- `byFacts` instantiates it at the goal (SW-4919).

theorem propHyp ∀ (h: ∀ (p: Prop) => p) (a: Prop): a := byFacts
