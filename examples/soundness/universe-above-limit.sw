-- expect-error: E-PARSE
-- One level above the largest universe, `Type 65535` (SW-902).
def above: Type 65536 := Type 65535
