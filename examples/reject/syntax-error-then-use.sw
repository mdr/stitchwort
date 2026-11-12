-- expect-error: E-PARSE
-- `broken`'s body fails to parse, but its header stands in for it: its uses
-- aren't `E-UNKNOWN-NAME`, and the unrelated type error is reported.
def broken (n: Nat): Nat := n +
def twice (n: Nat): Nat := broken (broken n)
def unrelated: Nat := "text"
