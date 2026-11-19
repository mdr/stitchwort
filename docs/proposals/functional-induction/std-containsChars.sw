import Std (Bool, Char, Eq, List, Nat, Text)

-- Names the principle so that it is made (the `match induct` below alone doesn't: SW-4229 finding B1).
theorem needIt ∀ (x: Nat): x = x :=
  let _ := Text.containsChars.induct
  byComputing

theorem allNotLineBreak ∀ (chars: List Char)
    (none: Text.containsChars ['\n'] chars = False):
    chars.all (char => char != '\n') = True :=
  match induct (Text.containsChars ['\n'] chars) with
    | eq1 => byComputing
    | eq2IfTrue char rest starts => cases
    | eq2IfFalse char rest starts ih => Bool.andIntro (cases) (ih none)
