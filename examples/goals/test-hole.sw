-- expect-test-failure: double
-- A test can have a hole too: it runs until it reaches the `?`, then stops
-- there and fails, saying which `?` it reached (D3777).
def double (n: Nat): Nat := n + n

test "double" := double 2 == ?
