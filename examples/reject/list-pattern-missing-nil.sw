-- expect-error: E-NONEXHAUSTIVE
-- Only non-empty lists are matched: the empty one is missing.
def f: List Nat -> Nat
  | [x] => x
  | [x, y] => y
  | Cons x (Cons y (Cons z rest)) => z
