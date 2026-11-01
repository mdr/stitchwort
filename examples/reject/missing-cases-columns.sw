-- expect-error: E-NONEXHAUSTIVE
-- Several arguments: each missing case is a row, one pattern per argument,
-- and a list's missing cases are in list syntax.
def zip: List Nat → List Nat → Nat
  | [], [] => 0
  | [_], [_] => 1
