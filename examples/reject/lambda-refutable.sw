-- expect-error: E-LET-REFUTABLE
-- A lambda's pattern parameter must cover every value of its type.
def nums (ms: List (Maybe Nat)): List Nat := List.map (\(Just x) => x) ms
