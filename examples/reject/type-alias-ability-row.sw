-- expect-error: E-PARSE
-- After `type World =`, `{` starts a record type's fields, so `IO` looks like
-- a field name. The braces hold an ability row, which can't be named yet: write
-- it where it's used instead.
type World = {IO, Fail}

def main: Nat := 0
