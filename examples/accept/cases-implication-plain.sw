-- `cases` applies a hypothesis `a → b` between plain propositions, as it
-- does one whose premise is an equation, where nothing else closes the case
-- (SW-4485; docs/syntax.md, "cases"): the premise is a hypothesis or a part
-- of one, and an implication of several premises is applied to each in turn
-- while they are in scope. Implications are not chained: `b` added by one
-- isn't a premise for another.
theorem modusPonens ∀ (a b: Prop) (f: a → b) (x: a): b := cases

theorem onPart ∀ (a b c: Prop) (both: a ∧ b) (f: a → c): c ∧ b := cases

theorem twoPremises ∀ (a b c: Prop) (f: a → b → c) (x: a) (y: b): c := cases
