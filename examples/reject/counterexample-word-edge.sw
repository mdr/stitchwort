-- expect-error: E-REFL
-- A bug at 2^64, where a machine word ends: random inputs include numbers
-- at a word's edges (counterexample search stage 2).
def wrap (n: Nat): Nat := if n < 18446744073709551616 then n else 0

theorem wrapKeeps (n: Nat): wrap n = n := rfl
