-- expect-error: E-REFL
-- Messages show a call as it is written: a defaulted parameter left out
-- isn't shown, one given is shown by name, and a positional argument
-- after a call that left a default out applies its result, in brackets
-- (docs/proposals/signature-defaults.md §6.2, §6.3, §8.4).

def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := [start, stop, step]

def mix (a: Nat) (early: Nat := a) (late: Nat := 5): Nat := a + early + late

def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat := x => base * factor * x

theorem leftOut (a: Nat) (b: Nat): range (a + 1) b = [a, b, 1] := rfl

theorem given (a: Nat) (b: Nat): range a b (step := 3) = [a, b, 1] := rfl

theorem laterGiven (a: Nat) (x: Nat): mix a (late := x) = a := rfl

theorem resultApplied (x: Nat): (scaler 5) x = x := rfl
