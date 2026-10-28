-- expect-error: E-PARSE
-- An `if` can follow `=` without brackets, but not `+`: the note says to
-- bracket it.
def bonus (big: Bool) (n: Nat): Nat := n + if big then 10 else 0
