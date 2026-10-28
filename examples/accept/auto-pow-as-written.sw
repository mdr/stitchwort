-- `auto` proves a power of a positive base isn't 0 with the exponent a
-- successor: `Nat.pow 2 (Succ k)` computes one step, to `Nat.pow 2 k * 2`,
-- which the procedure for `Nat.pow (Succ b) e ≠ 0` doesn't fit, so it is
-- tried on the power as written.

import Std (Nat)

def halveThenDivide (n: Nat) (k: Nat): Nat := n / Nat.pow 2 (Succ k)

def remainderBy (n: Nat) (k: Nat): Nat := n % Nat.pow 3 (Succ (Succ k))

def needsNonzero (n: Nat) (k: Nat) [auto whole: Nat.pow 2 (Succ k) ≠ 0]: Nat := n / Nat.pow 2 (Succ k)

def passesNonzero (n: Nat) (k: Nat): Nat := needsNonzero n k

theorem halfDivided (n: Nat) (k: Nat): n / 2 / Nat.pow 2 k = n / Nat.pow 2 (Succ k) := Nat.halfDivPow n k

test "halveThenDivide" := halveThenDivide 100 2 == 12

test "remainderBy" := remainderBy 100 0 == 1

test "passesNonzero" := passesNonzero 64 1 == 16
