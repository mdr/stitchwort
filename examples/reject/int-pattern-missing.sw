-- expect-error: E-NONEXHAUSTIVE
-- Number patterns alone never cover every `Int`: there are always other
-- numbers, positive and negative.
def f: Int → Nat
  | 0 => 1
  | (-1) => 2
