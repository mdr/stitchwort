-- expect-error: E-TYPE-MISMATCH
-- A call with a parameter left out is a function; where a value is
-- expected, the note names what it's still waiting for
-- (docs/proposals/named-arguments.md §6.3).

def clampTo (low: Nat) (high: Nat) (value: Nat): Nat :=
  if value < low then low else if value > high then high else value

def capped: Nat := clampTo (high := 10)
