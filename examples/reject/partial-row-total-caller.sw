-- expect-error: E-PARTIAL

import Std (Fail)

-- Fails at 3, on its way down: partial.
def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Fail.fail "three" else if n == 0 then 0 else countdown (n - 1)

-- `Fail.toResult` around a partial program is partial too
-- (docs/proposals/partial-handlers.md §4, D1255), so a function whose type
-- doesn't say `Partial` can't run it.
def caught (n: Nat): Result Nat Text := Fail.toResult (() => countdown n)
