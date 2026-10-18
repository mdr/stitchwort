-- expect-error: E-PARSE
-- An annotation inside a tuple needs its own brackets.
def bad : (Nat, Nat) := (1, 2 : Nat)
