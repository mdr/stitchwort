-- expect-error: E-PARSE
-- A line starting with an operator continues the line above only from the
-- block's column rightwards; further left it is an error that says where.

def both (a b: Bool): Bool :=
    a
  ∧ b
