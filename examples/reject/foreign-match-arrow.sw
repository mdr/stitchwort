-- expect-error: E-PARSE
-- `->` is the function arrow; a match arm separates its pattern and body
-- with `=>`.
def zeroOr (n: Nat): Nat :=
  match n with
    | 0 -> 1
    | _ => n
