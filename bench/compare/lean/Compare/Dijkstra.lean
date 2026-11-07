import Std.Data.TreeSet
open Std

/-- The cave's risk levels, one digit per position, row by row. -/
structure Cave where
  height : Nat
  width : Nat
  levels : Array Nat

def parseCave (input : String) : Cave :=
  let rows := input.splitOn "\n" |>.filter (· ≠ "")
  let levels := rows.foldl (fun acc row => row.foldl (fun acc c => acc.push (c.toNat - '0'.toNat)) acc) #[]
  { height := rows.length, width := (rows.headD "").length, levels }

/-- A map of risk levels: the cave itself, or the cave tiled five times each
way with each tile's levels raised by its distance from the top left. -/
structure RiskMap where
  height : Nat
  width : Nat
  level : Nat → Nat → Nat

def Cave.risks (cave : Cave) : RiskMap :=
  { height := cave.height, width := cave.width,
    level := fun row column => cave.levels[row * cave.width + column]! }

def Cave.tiled (cave : Cave) : RiskMap :=
  { height := 5 * cave.height, width := 5 * cave.width,
    level := fun row column =>
      let base := cave.levels[(row % cave.height) * cave.width + column % cave.width]!
      let raised := base + (row / cave.height + column / cave.width)
      if raised > 9 then raised - 9 else raised }

/-- Dijkstra's search from the top left, which costs nothing, to the bottom
right. The queue is an ordered set of (distance, position) pairs packed into
one number, `distance * size + position`. -/
def RiskMap.lowestRisk (risks : RiskMap) : Nat := Id.run do
  let size := risks.height * risks.width
  let infinity := 1 <<< 60
  let mut distance : Array Nat := Array.replicate size infinity
  distance := distance.set! 0 0
  let mut queue : TreeSet Nat := TreeSet.empty.insert 0
  while !queue.isEmpty do
    let some key := queue.min? | break
    queue := queue.erase key
    let here := key % size
    let cost := key / size
    if cost > distance[here]! then continue
    let row := here / risks.width
    let column := here % risks.width
    let neighbours : List (Option (Nat × Nat)) :=
      [ if row > 0 then some (row - 1, column) else none,
        if row + 1 < risks.height then some (row + 1, column) else none,
        if column > 0 then some (row, column - 1) else none,
        if column + 1 < risks.width then some (row, column + 1) else none ]
    for neighbour in neighbours do
      if let some (r, c) := neighbour then
        let there := r * risks.width + c
        let through := cost + risks.level r c
        if through < distance[there]! then
          distance := distance.set! there through
          queue := queue.insert (through * size + there)
  return distance[size - 1]!

def main : IO Unit := do
  let stdin ← IO.getStdin
  let cave := parseCave (← stdin.readToEnd)
  IO.println s!"Part 1: {cave.risks.lowestRisk}"
  IO.println s!"Part 2: {cave.tiled.lowestRisk}"
