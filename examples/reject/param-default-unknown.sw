-- expect-error: E-UNKNOWN-NAME
-- A name the function doesn't have: the note lists its parameters, with
-- their defaults (docs/proposals/signature-defaults.md §8.3).

def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def numbers: List Nat := range 0 10 (stride := 2)
