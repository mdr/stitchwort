-- A test can have a hole too: it's unfinished, so it doesn't run.
def double (n: Nat): Nat := n + n

test "double" := double 2 == ?
