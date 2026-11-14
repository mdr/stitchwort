-- expect-test-failure: double
-- A test can have a hole too: its code reaches the unfinished `?`, so it
-- fails and says which `?` it needs (SW-2909).
def double (n: Nat): Nat := n + n

test "double" := double 2 == ?
