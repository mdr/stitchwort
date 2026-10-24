-- expect-error: E-PARSE
-- Defaults are on record and constructor fields, not on a function's
-- parameters (docs/proposals/named-arguments.md §5.4, D1097).

def range (start: Nat) (stop: Nat) (step: Nat := 1): Nat := stop - start + step
