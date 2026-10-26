-- expect-error: E-PARSE
-- A lambda's parameter can't have a default: there's no declaration for
-- it to belong to (docs/proposals/signature-defaults.md §5.1).

def addOne: Nat -> Nat := (x: Nat := 0) => x + 1
