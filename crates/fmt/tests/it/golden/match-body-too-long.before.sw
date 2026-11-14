-- R: a match body goes on the header line when it fits (D1014), otherwise
-- on the next line at +2, with the arms at +2 from the `match` line.
theorem longHeader (first: Nat) (second: Nat) (third: Nat) (fourth: Nat) (fifth: Nat) (sixth: Nat) (seventh: Nat): first + second + third + fourth + fifth + sixth + seventh = seventh + sixth + fifth + fourth + third + second + first := match first with
  | Zero => rfl
  | Succ k => rfl
