-- expect-error: E-PARSE
-- A keyword can't be a parameter's name.
def pick (condition: Bool) (then: Nat): Nat := then
