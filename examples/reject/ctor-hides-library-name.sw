-- expect-error: E-NOT-A-FUNCTION
-- A constructor named like a library type hides it; the error says which
-- declaration the name found and that the library's is hidden.

type Gate = | And | Or

def both (p: Prop) (q: Prop): Prop := And p q
