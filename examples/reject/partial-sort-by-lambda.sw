-- expect-error: E-PARTIAL
-- The same with a lambda: the note is about the callback's type, not the
-- enclosing function.
import Std (List, Nat, Ord)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def sorted (numbers: List Nat): {Partial} (List Nat) := List.sortBy numbers (x y => Ord.compare (collatzSteps x) (collatzSteps y))
