inductive Instruction where
  | mul (left right : Nat)
  | doIt
  | dont

/-- Up to three digits from `position`: the number and the position after it. -/
def shortNumber (memory : ByteArray) (position : Nat) : Option (Nat × Nat) := Id.run do
  let mut end_ := position
  let mut value := 0
  while end_ < memory.size && end_ < position + 3 && memory[end_]! >= 48 && memory[end_]! <= 57 do
    value := value * 10 + (memory[end_]!.toNat - 48)
    end_ := end_ + 1
  if end_ == position then none else some (value, end_)

def hasAt (memory : ByteArray) (position : Nat) (text : String) : Bool :=
  let bytes := text.toUTF8
  position + bytes.size <= memory.size && (List.range bytes.size).all fun i => memory[position + i]! == bytes[i]!

/-- The instruction at `position`, with the position after it. -/
def instructionAt (memory : ByteArray) (position : Nat) : Option (Instruction × Nat) :=
  if hasAt memory position "mul(" then
    match shortNumber memory (position + 4) with
    | some (left, afterLeft) =>
      if hasAt memory afterLeft "," then
        match shortNumber memory (afterLeft + 1) with
        | some (right, afterRight) =>
          if hasAt memory afterRight ")" then some (.mul left right, afterRight + 1) else none
        | none => none
      else none
    | none => none
  else if hasAt memory position "do()" then some (.doIt, position + 4)
  else if hasAt memory position "don't()" then some (.dont, position + 7)
  else none

/-- Every instruction in the memory, skipping what isn't one a character at a time. -/
def parseInstructions (memory : ByteArray) : Array Instruction := Id.run do
  let mut found := #[]
  let mut position := 0
  while position < memory.size do
    match instructionAt memory position with
    | some (instruction, after) =>
      found := found.push instruction
      position := after
    | none => position := position + 1
  return found

def solvePart1 (instructions : Array Instruction) : Nat :=
  instructions.foldl (fun total instruction =>
    match instruction with
    | .mul left right => total + left * right
    | _ => total) 0

def solvePart2 (instructions : Array Instruction) : Nat :=
  (instructions.foldl (fun (enabled, total) instruction =>
    match instruction with
    | .mul left right => (enabled, if enabled then total + left * right else total)
    | .doIt => (true, total)
    | .dont => (false, total)) (true, 0)).2

def main : IO Unit := do
  let stdin ← IO.getStdin
  let instructions := parseInstructions (← stdin.readToEnd).toUTF8
  IO.println s!"Part 1: {solvePart1 instructions}"
  IO.println s!"Part 2: {solvePart2 instructions}"
