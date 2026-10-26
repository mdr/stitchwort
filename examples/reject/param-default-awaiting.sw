-- expect-error: E-TYPE-MISMATCH
-- A call still waiting for a required parameter is a function; the note
-- also says which defaults it filled
-- (docs/proposals/signature-defaults.md §8.3).

def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def numbers: List Nat := range 0
