-- expect-error: E-TYPE-MISMATCH
-- Like quot-relation-mismatch.sw, but the quotient is written through an alias
-- that takes the relation, so the message names the alias (`QBool AllTrue`); it
-- adds what that is, since `Quot Bool BoolEq` against it shows no difference.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def BoolEq (x: Bool) (y: Bool): Prop := x = y
def QBool (r: Bool -> Bool -> Prop): Type := Quot Bool r

def wrong (q: QBool AllTrue): Quot Bool BoolEq := (q : QBool AllTrue)
