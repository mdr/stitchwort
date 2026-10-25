-- expect-error: E-TYPE-MISMATCH
-- `List.sortBy` takes only total comparisons: its callback's type,
-- `Nat → Nat → Ordering`, has no `{e}` row, so a partial comparison is
-- refused, and the note says why from that type.
import Std (List, Nat, Ord, Ordering)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def bySteps (x: Nat) (y: Nat): {Partial} Ordering := Ord.compare (collatzSteps x) (collatzSteps y)

def sorted (numbers: List Nat): {Partial} (List Nat) := List.sortBy numbers bySteps
