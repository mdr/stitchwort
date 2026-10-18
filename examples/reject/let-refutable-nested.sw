-- expect-error: E-LET-REFUTABLE
-- A refutable pattern nested inside a tuple is still refutable.
firstOf : (Maybe Nat, Nat) -> Nat
firstOf p =
  let (Just a, b) = p
  a + b
