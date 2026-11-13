-- `Instruction.run` shares its short name with `Code.run`, which calls
-- `Code.runFrom`. In `runFrom`, `instruction` is bound by a pattern, with no
-- written type, but `Step`'s field is written `(instruction: Instruction)`, so
-- `instruction.run` means `Instruction.run` and `Code.runFrom` isn't in a
-- group with `Code.run`.
type Instruction = { by: Nat }
type Code = { limit: Nat }
type Progress = | Step (instruction: Instruction) (left: Nat)

def Instruction.run (instruction: Instruction) (n: Nat): Nat := n + instruction.by

def Code.runFrom (code: Code) (step: Progress) (n: Nat): Nat
    decreasing step.left
:= match step with
  | Step instruction left =>
    if h: 0 < left then Code.runFrom code (Step instruction (left - 1)) (instruction.run n) [decreasing := omega] else n

def Code.run (code: Code) (instruction: Instruction): Nat := code.runFrom (Step instruction code.limit) 0
