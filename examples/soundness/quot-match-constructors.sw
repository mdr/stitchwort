-- expect-error: E-TYPE-MISMATCH
-- R2 (docs/proposals/map-equality.md §7.5, §7.6): the carrier's
-- constructors don't match a quotient either; the message says to use
-- `Quot.lift`. Pairs with `constFalse` in accept/quot-forms.sw.
def AllTrue (x: Bool) (y: Bool): Prop := Unit
def Q: Type := Quot Bool AllTrue

def rep: Q -> Bool
  | False => False
  | True  => True
