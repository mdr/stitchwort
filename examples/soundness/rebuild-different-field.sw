-- expect-error: E-TERMINATION
-- `Succ j` uses the same constructor as the matched `Succ k`, but around a
-- different value, so it isn't a rebuilt descendant: `grow 2 5` would call
-- `grow 6 6`, and so on forever.
def grow: Nat -> Nat -> Nat
  | 0,             j => j
  | 1,             j => j
  | Succ (Succ k), j => grow (Succ j) (j + 1)
