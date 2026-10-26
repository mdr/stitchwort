-- expect-error: E-EXPORT
-- An exported function can't have a parameter default yet: JavaScript
-- callers will get them as an options object
-- (docs/proposals/signature-defaults.md §9, stage 2).

export def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]
