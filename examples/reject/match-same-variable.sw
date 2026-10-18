-- expect-error: E-MATCH-MOTIVE
-- The same variable can't be two scrutinees.
def twice (n : Nat) : Nat := 1 + match n, n with
  | Zero, _ => 0
  | Succ k, _ => k
