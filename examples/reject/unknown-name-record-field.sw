-- expect-error: E-UNKNOWN-NAME
-- A record's field is reached through a value (`x.bits`) or written in
-- full (`Float.bits`), so a bare name doesn't suggest the field accessor.
def x: Nat := bits
