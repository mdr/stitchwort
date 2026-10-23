-- expect-error: E-TYPE-MISMATCH
-- R11 (docs/proposals/map-equality.md §7.1 C4, §7.6): a lift's quotient must
-- be by the lift's own relation. The identity respects equality, but applied
-- to the quotient by `AllTrue` it would read the representative out. Pairs
-- with `unwrapEq` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def Q: Type := Quot Bool AllTrue

def unwrap (q: Q): Bool := Quot.lift [r := BoolEq] (b => b) (x y h => h) q
