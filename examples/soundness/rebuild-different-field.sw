-- expect-error: E-TERMINATION
-- `Succ j` uses the same constructor as the matched `Succ k`, but around a
-- different value, so it isn't a rebuilt descendant: `grow 2 5` would call
-- `grow 6 6`, and so on forever.
grow : Nat -> Nat -> Nat
grow 0               j = j
grow 1               j = j
grow (Succ (Succ k)) j = grow (Succ j) (j + 1)
