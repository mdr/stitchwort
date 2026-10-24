-- expect-error: E-PARTIAL

-- A test must finish: it can't run a computation that might not.
def spin (n: Nat): {Partial} Nat := spin (n + 1)

test "spins" := spin 0 == 0
