/-- The cavern: a rectangle of energy levels, row by row. -/
structure Cavern where
  height : Nat
  width : Nat
  levels : Array Nat

def parseCavern (input : String) : Cavern :=
  let rows := input.splitOn "\n" |>.filter (· ≠ "")
  let levels := rows.foldl (fun acc row => row.foldl (fun acc c => acc.push (c.toNat - '0'.toNat)) acc) #[]
  { height := rows.length, width := (rows.headD "").length, levels }

/-- How many of the eight octopuses around `index` have flashed. -/
def Cavern.flashersAround (cavern : Cavern) (flashed : Array Bool) (index : Nat) : Nat := Id.run do
  let row := index / cavern.width
  let column := index % cavern.width
  let mut count := 0
  for rowStep in [0:3] do
    for columnStep in [0:3] do
      if rowStep == 1 && columnStep == 1 then continue
      if row + rowStep < 1 || column + columnStep < 1 then continue
      let r := row + rowStep - 1
      let c := column + columnStep - 1
      if r < cavern.height && c < cavern.width && flashed[r * cavern.width + c]! then
        count := count + 1
  return count

/-- One round of a step: an octopus flashes if its level, plus 1, plus the
flashers around it so far, is above 9. -/
def Cavern.flashRound (cavern : Cavern) (flashed : Array Bool) : Array Bool :=
  Array.ofFn (n := cavern.levels.size) fun index =>
    9 < cavern.levels[index]! + 1 + cavern.flashersAround flashed index

/-- The octopuses that flash in a step: rounds until one adds nobody. -/
def Cavern.flashers (cavern : Cavern) : Array Bool := Id.run do
  let mut flashed := Array.replicate cavern.levels.size false
  for _ in [0:cavern.levels.size] do
    let next := cavern.flashRound flashed
    if next == flashed then break
    flashed := next
  return flashed

/-- One step: every octopus that flashed is at 0, the others at their energy. -/
def Cavern.step (cavern : Cavern) : Cavern :=
  let flashed := cavern.flashers
  { cavern with levels := Array.ofFn (n := cavern.levels.size) fun index =>
      if flashed[index]! then 0 else cavern.levels[index]! + 1 + cavern.flashersAround flashed index }

def Cavern.zeros (cavern : Cavern) : Nat := cavern.levels.foldl (fun n level => if level == 0 then n + 1 else n) 0

def Cavern.allZero (cavern : Cavern) : Bool := cavern.levels.all (· == 0)

def Cavern.flashesIn (cavern : Cavern) (steps : Nat) : Nat := Id.run do
  let mut cavern := cavern
  let mut total := 0
  for _ in [0:steps] do
    cavern := cavern.step
    total := total + cavern.zeros
  return total

/-- The first step after which every octopus is at 0, within `limit` steps. -/
def Cavern.firstSync (cavern : Cavern) (limit : Nat) : Option Nat := Id.run do
  let mut cavern := cavern
  for number in [1:limit + 1] do
    cavern := cavern.step
    if cavern.allZero then return some number
  return none

def main : IO Unit := do
  let stdin ← IO.getStdin
  let cavern := parseCavern (← stdin.readToEnd)
  IO.println s!"Part 1: {cavern.flashesIn 100}"
  match cavern.firstSync 10000 with
  | some step => IO.println s!"Part 2: {step}"
  | none => throw (IO.userError "no step within 10000 has every octopus flash")
