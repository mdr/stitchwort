-- expect-error: E-DEFAULT-POSITIONAL
-- A positional argument after the parameters ran out, in a call that left a
-- defaulted parameter out, could mean the default or the result applied to
-- it: an error with both fixes (docs/proposals/signature-defaults.md §6.3).

def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat := x => base * factor + x

def scaled: Nat := scaler 5 3
