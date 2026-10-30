-- expect-error: E-PARSE
-- An ability row is written only on a result type (D1141 (d)), so a
-- parameter's type can't start with one. `{} Nat` is `Nat`, so the error
-- says to leave the row out; for a computation, it says to take a function
-- returning one. Before SW-908, `{} Nat` here was read as an empty record
-- literal applied to `Nat` ("can't tell which record type this literal
-- is"), and `{IO} Nat` as a record update with no `|`.
def plain (c: {} Nat): Nat := c

def later (c: {IO} Nat): Nat := 0
