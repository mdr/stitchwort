-- expect-error: E-PARSE
-- SW-902: the wrapped step also put `Type 4294967294` in `Type 4294967295`.
def wrap2: Type 4294967295 := Type 4294967294
