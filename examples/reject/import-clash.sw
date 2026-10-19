-- expect-error: E-IMPORT-CLASH
-- This file defines its own `length`, which would hide the import completely.
import List (length)

def length: Nat := 0
