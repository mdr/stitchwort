-- expect-error: E-OLD-DECLARATION
-- The old declaration syntax, a signature line and then equations, is gone:
-- definitions start with `def`.
double : Nat -> Nat
double n = n + n
