-- expect-error: E-PARSE
-- An annotation inside a tuple needs its own brackets.
bad : (Nat, Nat)
bad = (1, 2 : Nat)
