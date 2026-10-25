-- `List.map` with a partial callback: the map is partial too, so the caller
-- says `Partial`. Here `main` does, and so do the helpers (partial-stage-3.md
-- §2.2, D1218). Tests may call partial code (D1183).
import Std (IO, List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def stepsOfAll (numbers: List Nat): {Partial} (List Nat) := List.map numbers collatzSteps

def stepsOfRows (rows: List (List Nat)): {Partial} (List (List Nat)) :=
  List.map rows (row => List.map row collatzSteps)

def main: {IO, Partial} () := IO.print (Nat.toText (List.sum (stepsOfAll [3, 7, 27])))

test "map with a partial callback" := stepsOfAll [3, 7, 27] == [7, 16, 111]
test "nested partial map" := stepsOfRows [[3], [7, 27]] == [[7], [16, 111]]
