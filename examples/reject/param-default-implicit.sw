-- expect-error: E-PARSE
-- Only an explicit parameter of a definition's header can have a default
-- (docs/proposals/signature-defaults.md §5.1).

def repeat [count: Nat := 2] (x: Nat): List Nat := List.replicate count x
