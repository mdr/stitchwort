-- expect-error: E-MATCH-MOTIVE
-- One scrutinee mentions another (`n`), so they overlap.
overlap : Nat -> Nat
overlap n = 1 + match Succ n, Succ (Succ n) with
  | _, _ -> 0
