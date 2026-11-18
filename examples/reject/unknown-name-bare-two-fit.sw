-- expect-error: E-UNKNOWN-NAME
-- Both `Std.Float.abs` and `Std.Int.abs` take one explicit argument, so the
-- call `abs 42` can't tell them apart: the hint keeps both names rather than
-- picking one and offering its import (SW-3978).
def main(): () := abs 42
