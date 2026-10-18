-- expect-error: E-LET-REFUTABLE
-- A lambda's pattern parameter must cover every value of its type.
nums : List (Maybe Nat) -> List Nat
nums ms = List.map (\(Just x) -> x) ms
