-- expect-error: E-PARTIAL
-- The same with a lambda: the note is about the callback, not the enclosing function.
import Std (List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def f (numbers: List Nat): {Partial} (List Nat) := List.filter numbers (n => collatzSteps n == 0)
