-- expect-error: E-NONEXHAUSTIVE
-- On a list of characters too, there's always another list.
def token: List Char → Nat
  | "->" => 1
  | "=>" => 2
