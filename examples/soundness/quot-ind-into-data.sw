-- expect-error: E-UNIVERSE
-- R6 (docs/proposals/map-equality.md §7.6): `Quot.ind` proves propositions
-- only. Into data, it would read the representative out without a proof that
-- the result respects the relation. Pairs with `allSame` in
-- accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def unwrap (q: Q): Bool := Quot.ind [p := q => Bool] (b => b) q
