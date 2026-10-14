-- expect-error: E-EXPORT
-- `twice'` is a fine Stitchwort name, but not a JavaScript identifier.
export
twice' : Nat -> Nat
twice' n = n + n
