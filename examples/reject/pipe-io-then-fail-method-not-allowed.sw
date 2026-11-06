-- expect-error: E-ABILITY
-- `toNatOrFail` fails, and the function may only use `IO`.

import Std (IO, List, Text)

def turns(): {IO} Nat :=
  IO.args() |> .headOr "2020" |> .toNatOrFail

def boundTurns(): {IO} Nat :=
  let l := IO.args()
  l.headOr "2020" |> .toNatOrFail
