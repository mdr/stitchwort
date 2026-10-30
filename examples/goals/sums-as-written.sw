-- A sum stuck on an unknown is shown with its number on the right, as it's
-- written: `x + 1` and `x + 3`, though `+` computes them to `Succ x` and
-- `3 + x` (SW-895). A `Succ` written as one, in the source or a pattern,
-- stays `Succ`.
theorem plusOne (x: Nat): x + 1 = 1 + x := ?

theorem plusThree (x y: Nat): x + 3 = y + (x + 2) := ?

theorem written (n: Nat): Succ n = Succ (Succ n) := ?

theorem matched (n: Nat): n = 0 := match n with
  | Zero => rfl
  | Succ m => ?
