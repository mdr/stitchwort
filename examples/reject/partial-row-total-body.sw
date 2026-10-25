-- expect-error: E-PARTIAL

import Std (Fail)
import Std.Effect (Effects)

-- A job kept in a data type: its row `e` is an argument of the type, so it
-- stands for total rows only.
type Job (e: Effects): Type =
  | MkJob (run: () → {Fail | e} Nat)

def runJob (job: Job e): {e} Nat := Fail.orElse 0 (Job.run job)

-- `viaJob` uses `e` only in rows, but its body stores `f` in a `Job`, so it
-- is checked again with `e` total (D1215): it takes only total callbacks.
def viaJob (f: () → {Fail | e} Nat): {e} Nat := runJob (MkJob f)

test "a total callback" := viaJob (() => 4) == 4

def spin (n: Nat): {Fail, Partial} Nat := spin (n + 1)

def partialJob(): {Partial} Nat := viaJob (() => spin 0)
