-- expect-error: E-TYPE-MISMATCH
-- The aim is written `≠`, not `!=`, so the `!=` note must not appear even
-- though the hypothesis mentions a `Bool` `!=` (SW-3125).
def neSymm (a: Nat) (b: Nat) (h: ((a != b): Bool) = True): (a ≠ b) = (b ≠ a) := h
