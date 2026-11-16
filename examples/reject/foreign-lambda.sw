-- expect-error: E-PARSE
-- `λ` isn't a Stitchwort character: a lambda is written `x => body`.
def inc: Nat -> Nat := λ x => x + 1
