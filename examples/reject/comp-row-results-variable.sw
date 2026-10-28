-- expect-error: E-TYPE-MISMATCH
-- A `Comp` whose operations are the empty row's but whose results are a
-- variable `r` (bound automatically) isn't a computation in the empty row:
-- the row's results are `NoRes`, and `r` might be anything. So the body, a
-- plain value, isn't made into one, and the elaborator says so with a note
-- on the row, rather than the kernel refusing what it made (SW-851). The
-- type that checks is `Comp NoOp NoRes Nat`, or `{} Nat`
-- (accept/empty-row-run.sw).
import Std.Effect (Comp, NoOp)

def next (n: Nat): Comp NoOp r Nat := n + 1
