-- expect-error: E-NONEXHAUSTIVE
-- A text column inside a constructor: the gap is in `Some _` only.
def pick: Option Text → Nat
  | Some "a" => 1
  | Some "b" => 2
  | None => 3
