-- expect-error: E-EXPORT
-- `delete` is a fine Stitchwort name, but reserved in JavaScript, so it
-- couldn't be imported by name.
export
delete : Nat -> Nat
delete n = n
