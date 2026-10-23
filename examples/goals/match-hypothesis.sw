-- `match h: …` names an equation about what's matched: it's in the
-- context, with the branch's constructor.
def describe (xs: List Nat): Text := match h: xs.length with
  | Zero => "empty"
  | Succ k => ?
