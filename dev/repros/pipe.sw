import Std (Fail, IO, List, Text)

def main(): {IO, Fail} () :=
  let turns := IO.args() |> .headOr "2020" |> .toNatOrFail
  IO.print "${turns}"
