-- expect-error: E-TYPE-MISMATCH
-- The hypothesis is already the `Bool` test `((a != b): Bool) = True`, and
-- `.read` gives the test's reading, not the goal's proposition: the note
-- must not tell the user to write the form they wrote (SW-3125).
import Std (Bool)

def neSymm (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a != b) = (b != a) := h.read
