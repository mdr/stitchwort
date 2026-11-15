-- Chapter 11: a `main` that chooses its exit status.
--
--   $ stitchwort run exit-status.sw -- notes.txt; echo $?

import Std (ExitStatus, IO, List, Text)

-- begin main
-- 0: nothing to fix; 1: something to fix; 3: no file named.
def verdict (arguments: List Text): ExitStatus := match arguments with
  | [] => ExitStatus.of 3
  | ["clean", ..rest] => ExitStatus.success
  | _ => ExitStatus.failure

def main(): {IO} ExitStatus :=
  let status := verdict (IO.args ())
  IO.print "exit status ${status}"
  status
-- end main

test "no file named" := (verdict []).toNat == 3
test "a clean file" := verdict ["clean"] == ExitStatus.success
test "anything else" := (verdict ["notes.txt"]).toNat == 1
