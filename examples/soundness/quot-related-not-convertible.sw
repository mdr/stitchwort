-- expect-error: E-REFL
-- R8 (docs/proposals/map-equality.md §7.2, §7.6): conversion is structural,
-- so related representatives aren't the same value: their equality is
-- `Quot.sound`'s, not `rfl`'s. Pairs with `same` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

theorem same: (Quot.mk False: Q) = Quot.mk True := rfl
