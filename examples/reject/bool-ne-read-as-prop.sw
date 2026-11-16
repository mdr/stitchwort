-- expect-error: E-TYPE-MISMATCH
-- A `Bool` `!=` beside `=` in a statement is the proposition `≠`, and the
-- hypothesis is already the `Bool` test `((a != b): Bool) = True`, so no
-- note tells the user to write the form they wrote (SW-3125).
def neSymm (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a != b) = (b != a) := h
