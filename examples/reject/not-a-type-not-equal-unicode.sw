-- expect-error: E-NOT-A-TYPE
-- Written `≠`, so the message quotes `≠`, not `!=` (SW-3125).
theorem notEqualIsNot (a: Nat) (b: Nat) (d: Bool): (a ≠ b) = !d := byComputing
