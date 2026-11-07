/-- The number spoken on `turn` (counting from 1) in the elves' memory game.
`lastSeen` holds, by number, the latest turn before the current one on which it
was spoken, 0 if none; it is updated in place. -/
def numberSpoken (starting : Array Nat) (turn : Nat) : Nat := Id.run do
  if turn == 0 then return 0
  let count := starting.size
  let room := turn + starting.foldl max 0 + 1
  let mut lastSeen : Array Nat := Array.replicate room 0
  let mut last := starting[0]!
  for current in [1:turn] do
    let before := lastSeen[last]!
    lastSeen := lastSeen.set! last current
    last := if current < count then starting[current]! else if before == 0 then 0 else current - before
  return last

def main (args : List String) : IO Unit := do
  let turns ← match args with
    | [] => pure 30000000
    | [text] => match text.toNat? with
      | some turns => pure turns
      | none => throw (IO.userError "expected no arguments, or the number of turns for part 2")
    | _ => throw (IO.userError "expected no arguments, or the number of turns for part 2")
  let stdin ← IO.getStdin
  let starting := (← stdin.readToEnd).trimAscii.toString.splitOn "," |>.map String.toNat! |>.toArray
  IO.println s!"Part 1: {numberSpoken starting 2020}"
  IO.println s!"Part 2: {numberSpoken starting turns}"
