-- expect-error: E-IMPORT-CLASH
-- This file defines its own `length`, which would hide the import completely.
import List (length)

length : Nat
length = 0
