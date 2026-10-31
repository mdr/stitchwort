-- expect-error: E-TYPE-MISMATCH
-- Like mismatch-alias-unfolded.sw, but the aliases are inside the types (SW-845):
-- `List Q` against `List Other` names two aliases and shows no difference, so the
-- message says what each one is.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def Q: Type := Quot Bool AllTrue
def Other: Type := Quot Bool BoolEq

def wrong (q: List Q): List Other := q
