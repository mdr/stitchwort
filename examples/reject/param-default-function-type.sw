-- expect-error: E-PARSE
-- A function type's parameter can't have a default
-- (docs/proposals/signature-defaults.md §5.1).

def apply (f: (x: Nat := 0) -> Nat): Nat := f 1
