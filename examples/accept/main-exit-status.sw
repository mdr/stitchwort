import Std (ExitStatus, IO)

-- A `main` that returns an `ExitStatus`: the program ends with that status.
-- No input is status 3, "ok" is 0 and anything else is 1.
def main(): {IO} ExitStatus :=
  IO.print "checking"
  match IO.readLine () with
    | None => ExitStatus.of 3
    | Some "ok" => ExitStatus.success
    | Some _ => ExitStatus.failure
