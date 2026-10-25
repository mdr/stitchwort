-- expect-error: E-AMBIGUOUS
-- A function type may repeat a parameter name; naming it then can't tell
-- the two apart (docs/proposals/named-arguments.md §4.3).

def apply (h: (x: Nat) → (x: Nat) → Nat): Nat := h (x := 1) 2
