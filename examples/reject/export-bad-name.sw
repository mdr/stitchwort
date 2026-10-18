-- expect-error: E-EXPORT
-- `twice'` is a fine Stitchwort name, but not a JavaScript identifier.
export def twice' (n : Nat) : Nat := n + n
