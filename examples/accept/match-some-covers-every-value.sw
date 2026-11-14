-- expect-warning: W-MATCH-TOTAL
-- Arms that match every value leave no value for the `None` that
-- `match some` adds, and the same for `False` in `matches`: the warning says
-- to write a `match` (and a `map`).
import Std (List, Nat, Bool)

type Scan = | Corrupted (illegal: Nat) | Incomplete (missing: Nat)

def values (scans: List Scan): List Nat := scans.filterMap (match some
  | Corrupted n => n
  | Incomplete n => n)

def always: Nat → Bool := matches | _ => True

test "values" := values [Corrupted 1, Incomplete 2] == [1, 2]
test "always" := always 3
