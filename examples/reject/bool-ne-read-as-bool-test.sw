-- expect-error: E-TYPE-MISMATCH
-- The hypothesis is already the `Bool` test `((a != b): Bool) = True`, so
-- the mismatch must not tell the user to write it (SW-3125).
import Std (Bool)

def neSymm (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a != b) = (b != a) := h.read
