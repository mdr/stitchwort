-- expect-error: E-TYPE-MISMATCH
-- Tuples print back as written: `(Nat, Bool, Text)`, not `Pair Nat (Pair Bool Text)`.
def bad : (Nat, Bool, Text) := (1, True)
