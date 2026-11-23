-- Both sides are proofs of `Unit`, a proposition here, so they are equal by
-- rule I (docs/core.md, "Proof irrelevance"), not by any computation rule
-- for `Quot.ind`: it still has none, and is frozen (rule F). The worry of
-- docs/proposals/map-equality.md §7.3, that such a rule would make any two
-- proofs of a proposition equal, is now the rule itself. Pairs with
-- `indItself` in accept/quot-forms.sw.
-- Was soundness/quot-ind-computes.sw, refused (E-REFL) before rule I (stage 5
-- of docs/proposals/full-proof-irrelevance.md).
def AllTrue (x y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

theorem computes: Quot.ind [p := q => Unit] (b => Trivial) (Quot.mk False: Q) = Trivial := byComputing
