-- A goal part `b → c` that an implication `f: a → b → c` gives once `x: a`
-- is applied, beside a part (`e`) that needs `g z` in the same case (SW-4510;
-- the partial application `f x` is what `cases` has to see, as a fact or by
-- introducing `b`).
theorem partial ∀ (a b c d e: Prop) (f: a → b → c) (g: d → e) (x: a) (z: d): (b → c) ∧ e := cases
