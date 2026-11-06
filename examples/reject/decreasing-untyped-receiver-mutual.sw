-- expect-error: E-DECREASING
-- `c` has no written type (a `let` binder), so `c.run` is linked to every
-- `.run`, and the error says the group may come from that. Here it is real:
-- `c` is a `Code`, and `Code.run` calls `Code.runFrom` back.
type Instruction = { by: Nat }
type Code = { limit: Nat }

def Instruction.run (instruction: Instruction) (n: Nat): Nat := n + instruction.by

def Code.runFrom (code: Code) (left: Nat) (n: Nat): Nat
    decreasing left
:=
  let c := code
  if h: 0 < left then Code.runFrom code (left - 1) (c.run) [decreasing := omega] else n

def Code.run (code: Code) (n: Nat): Nat := Code.runFrom code code.limit n
