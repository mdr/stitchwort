-- expect-error: E-PROOF-ONLY
-- A `test` runs, so it can't use `reify`.
import Std (Fail)

test "finished" :=
  match reify (() => Fail.need (Some 3) "none") with
    | return x => True
    | Fail.stop msg, _ => False
