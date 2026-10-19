-- expect-error: E-MATCH-MOTIVE
-- One scrutinee mentions another (`n`), so they overlap.
def overlap (n: Nat): Nat := 1 + match Succ n, Succ (Succ n) with
  | _, _ => 0
