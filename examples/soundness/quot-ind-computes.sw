-- expect-error: E-REFL
-- R7 (docs/proposals/map-equality.md §7.3, §7.6): `Quot.ind` has no
-- computation rule. With one, any two proofs of a proposition would be
-- provably equal. Pairs with `indItself` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

theorem computes:
    Quot.ind [p := q => Unit] (b => Trivial) (Quot.mk False: Q) = Trivial := rfl
