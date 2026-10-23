-- expect-error: E-TYPE-MISMATCH
-- R5 (docs/proposals/map-equality.md §7.6): the only way from a quotient to
-- data is `Quot.lift`, with a proof that the function respects the
-- relation. For the identity on `Bool` by `AllTrue` that's `x = y` for every
-- `x` and `y`, which is false, so the relation's own proof doesn't do.
-- Pairs with `constFalse` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def unwrap (q: Q): Bool := Quot.lift (b => b) (x y related => related) q
