-- expect-error: E-LET-REFUTABLE
-- A number pattern only matches that number.
def zero (n : Nat) : Nat :=
  let 0 := n
  1
