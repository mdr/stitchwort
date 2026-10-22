-- expect-error: E-PARSE
-- `broken` fails to parse, but its name is declared as failed: the uses of
-- it are not `E-UNKNOWN-NAME`, and the unrelated type error is reported.
def broken (n: Nat): Nat := n +
def twice (n: Nat): Nat := broken (broken n)
def unrelated: Nat := "text"
