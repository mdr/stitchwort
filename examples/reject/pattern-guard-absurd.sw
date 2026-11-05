-- expect-error: E-PARSE
-- An absurd arm tests nothing, so it can't have a condition.

type Empty: Type

def fromEmpty: Empty → Nat
  | () if True
