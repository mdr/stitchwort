-- expect-error: E-TYPE-MISMATCH
-- A `Bool` `!=` beside `=` in a statement is the proposition `≠`, so the
-- `Bool` hypothesis doesn't prove it; the note says how to write the `Bool`.
def neSymm (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a != b) = (b != a) := h
