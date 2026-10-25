-- expect-error: E-TYPE-MISMATCH
-- `List.filter` takes only total predicates; unlike `map`, its callback is
-- not in a bare row, so a partial predicate is refused.
import Std (List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def isTrivial (n: Nat): {Partial} Bool := collatzSteps n == 0

def trivialOnes (numbers: List Nat): {Partial} (List Nat) := List.filter numbers isTrivial
