-- expect-error: E-FACTS
-- A hypothesis concluding in a bare variable of a `Type` binder gives data,
-- not a proof, so `byFacts` doesn't collect it: nothing proves `b`
-- (SW-4919).

theorem dataHyp ∀ (h: ∀ (t: Type) => t) (a b: Prop) (x: a): b := byFacts
