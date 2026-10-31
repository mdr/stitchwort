-- expect-error: E-IMPORT-CLASH
-- A name imported under another name clashes with a declaration of that
-- name, as any import does.
import Std.List (length as count)

def count: Nat := 3
