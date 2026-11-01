-- expect-error: E-UNKNOWN-FIELD
-- A record update starting a theorem's statement is read as a record, not an
-- ability row (SW-1015), so a misspelt field is reported as one.

import Std (Eq, Nat)

type Point = { id: Nat, x: Nat }

theorem misspelt (p: Point): { p | y = 3 }.x = p.x := rfl
