-- expect-error: E-UNKNOWN-FIELD
-- `xs |> .dorp 1` is `xs.dorp 1`, so it's the ordinary dot-notation error:
-- `List` has no `dorp` (the note suggests `drop`).

def f (xs: List Nat): List Nat := xs |> .dorp 1
