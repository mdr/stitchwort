-- expect-error: E-UNIVERSE
-- R9 (docs/proposals/map-equality.md §7.1, §7.6): a quotient's carrier is a
-- type, never a proposition. Pairs with `QProp` in accept/quot-forms.sw,
-- whose carrier is the universe `Prop` itself.
def T: Type := Quot (0 = 0) (x y => Unit)
