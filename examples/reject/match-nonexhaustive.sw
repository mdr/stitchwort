-- expect-error: E-NONEXHAUSTIVE
-- A `match` must cover every case.
def nonExhaustive (xs: List Nat): Nat := 1 + match xs with
  | Nil => 0
