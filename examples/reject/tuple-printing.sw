-- expect-error: E-TYPE-MISMATCH
-- Tuples print back as written: `(Nat, Bool, Text)`, not `Pair Nat (Pair Bool Text)`.
bad : (Nat, Bool, Text)
bad = (1, True)
