-- `auto` proves a divisor isn't 0 from a fact in scope that it's at least
-- 1, and a power of a positive base through a definition that unfolds to one.

import Std (Nat)

def remainder (n: Nat) (d: Nat) (positive: 0 < d): Nat := n % d

def half (n: Nat) (d: Nat) (big: 2 ≤ d): Nat := n / d

def quotientIfPositive (n: Nat) (d: Nat): Nat := if positive: 0 < d then n / d else 0

def fromLet (n: Nat) (d: Nat) (big: 3 ≤ d): Nat :=
  let positive: 1 ≤ d := Nat.leTrans 1 3 d rfl big
  n % d

-- 10 to the power of the number of digits.
def placeValue (number: Nat): Nat := Nat.pow 10 (Nat.digitCount number)

def lastDigits (n: Nat) (number: Nat): Nat := n % placeValue number

test "remainder" := remainder 17 5 rfl == 2

test "lastDigits" := lastDigits 12345 678 == 345
