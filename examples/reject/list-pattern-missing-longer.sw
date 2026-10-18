-- expect-error: E-NONEXHAUSTIVE
-- Lists of two or more elements aren't matched.
def f : List Nat -> Nat
  | [] => 0
  | [x] => x
