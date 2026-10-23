-- expect-error: E-RECORD-UPDATE
-- The implicit `h` mentions `n`, so `n` cannot be updated.

type Labelled =
  | LA (n: Nat) [h: n = 0] (label: Text)
  | LB (n: Nat) [h: n = 0] (label: Text)

def f (a: Labelled): Labelled := { a | n = 1 }
