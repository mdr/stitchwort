-- A dot call that performs `Fail`, on a receiver that performs `IO`, in a
-- function allowed both.

import Std (Fail, IO, List, Text)

def turns(): {IO, Fail} Nat := IO.args() |> .headOr "2020" |> .toNatOrFail

def turnsInBrackets(): {IO, Fail} Nat := (IO.args().headOr "2020").toNatOrFail

def main(): {IO, Fail} () := IO.print "${turns() + turnsInBrackets()}"
