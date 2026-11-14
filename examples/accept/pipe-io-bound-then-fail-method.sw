-- A dot call that performs `Fail`, on a receiver whose type is a type
-- parameter of the call before it (`headOr`'s `a`, here `Text`), in a function
-- allowed it.

import Std (Fail, IO, List, Text)

def firstTurn (l: List Text): {Fail} Nat := l.headOr "2020" |> .toNatOrFail

def turns(): {IO, Fail} Nat :=
  let l := IO.args()
  l.headOr "2020" |> .toNatOrFail

def turnsInBrackets(): {IO, Fail} Nat :=
  let l := IO.args()
  (l.headOr "2020").toNatOrFail

def main(): {IO, Fail} () := IO.print "${turns() + turnsInBrackets() + firstTurn []}"
