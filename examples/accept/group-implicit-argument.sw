-- A group whose type takes an implicit argument, `(a b: Box)`, is
-- shorthand for `(a: Box) (b: Box)`: each name gets its own `t`, so `a`
-- can hold numbers and `b` booleans (D3679).
def Box [t: Type]: Type := List t

def p: Prop := ∀ (a b: Box) => a = [1] ∧ b = [True]
