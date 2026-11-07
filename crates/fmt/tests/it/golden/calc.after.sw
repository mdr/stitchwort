-- R14: `calc` steps at +2, each `_ = … := …` on its own line.
theorem calcStep (a: Nat) (b: Nat) (h: a + 2 <= b): a < b :=
  calc a
    _ < a + 1 := omega
    _ <= b := omega

theorem long (a: Nat) (b: Nat): a + 0 + 0 = a :=
  calc a + 0 + 0
    _ = a + 0
      := Nat.addZero a
    _ = a := Nat.addZero a
