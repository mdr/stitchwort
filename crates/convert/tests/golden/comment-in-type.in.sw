-- A comment inside the signature's type, in the part that would become
-- header binders (5.3 rule 5: must not be dropped).

h : Nat ->
  -- a comment inside the type
  Nat -> Nat
h a b = a
