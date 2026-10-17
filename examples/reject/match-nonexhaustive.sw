-- expect-error: E-NONEXHAUSTIVE
-- A `match` must cover every case.
nonExhaustive : List Nat -> Nat
nonExhaustive xs = 1 + match xs with
  | Nil -> 0
