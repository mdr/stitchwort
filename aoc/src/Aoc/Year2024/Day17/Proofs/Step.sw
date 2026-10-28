-- Each step of the program is the puzzle's: for every program and machine,
-- `Machine.step` takes the step `StepMatches` describes (`stepMatches`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (Bool, Eq, Exists, List, Nat, Option)

-- The program's combo operands stand for what the puzzle's do.
theorem comboAgrees (registers: Registers): (operand: Nat) → Option.map (comboOperand operand) registers.value = comboValue registers operand
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ operand)))))) => rfl

-- `Nat.xor` is the puzzle's bitwise XOR.
theorem xorBitwise (x: Nat) (y: Nat): BitwiseXor x y (x.xor y) :=
  i =>
    Eq.trans (Eq.sym (Nat.testBitDiv (x.xor y) i))
      (Eq.trans (Nat.testBitXor i x y) (rewrite Nat.testBitDiv x i, Nat.testBitDiv y i in rfl))

-- An instruction with a combo operand, made by `make`, does what `happens`
-- says of the operand's value.
theorem comboStep (machine: Machine) (operand: Nat) (make: Combo → Instruction) (after: Nat → Machine) (printed: Nat → Option Nat)
    (executes: (combo: Combo) → machine.execute (make combo) = Next (after (machine.registers.value combo)) (printed (machine.registers.value combo))):
    WithCombo machine.registers operand
      (match Option.map (comboOperand operand) make with
        | Some instruction => machine.execute instruction
        | None => Fault)
      (value =>
        (match Option.map (comboOperand operand) make with
          | Some instruction => machine.execute instruction
          | None => Fault) = Next (after value) (printed value)) :=
  let agrees := comboAgrees machine.registers operand
  match found: comboOperand operand with
    | None => rewrite Eq.sym agrees in rfl
    | Some combo => rewrite Eq.sym agrees in executes combo

-- Each opcode, with each operand, does what the puzzle says.
theorem executesDecode (operand: Nat) (machine: Machine): (opcode: Nat) →
    Executes opcode operand machine
      (match decode opcode operand with
        | Some instruction => machine.execute instruction
        | None => Fault)
  | 0 =>
    comboStep machine operand Adv (value => advanced machine { machine.registers | a = machine.registers.a / Nat.pow 2 value }) (value => None)
      (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo) in rfl)
  | 1 => Witness (machine.registers.b.xor operand) (Both (xorBitwise machine.registers.b operand) rfl)
  | 2 => comboStep machine operand Bst (value => advanced machine { machine.registers | b = value % 8 }) (value => None) (combo => rfl)
  | 3 =>
    match zero: machine.registers.a == 0 with
      | True => rfl
      | False => rfl
  | 4 => Witness (machine.registers.b.xor machine.registers.c) (Both (xorBitwise machine.registers.b machine.registers.c) rfl)
  | 5 => comboStep machine operand Out (value => advanced machine machine.registers) (value => Some (value % 8)) (combo => rfl)
  | 6 =>
    comboStep machine operand Bdv (value => advanced machine { machine.registers | b = machine.registers.a / Nat.pow 2 value }) (value => None)
      (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo) in rfl)
  | 7 =>
    comboStep machine operand Cdv (value => advanced machine { machine.registers | c = machine.registers.a / Nat.pow 2 value }) (value => None)
      (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo) in rfl)
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ opcode))))))) => rfl

-- Every step the program takes is the puzzle's.
theorem stepMatches (program: List Nat) (machine: Machine): StepMatches program machine (machine.step program) :=
  match fetched: program.get machine.pointer with
    | None => rfl
    | Some opcode =>
      match operandFetched: program.get (machine.pointer + 1) with
        | None => rfl
        | Some operand => executesDecode operand machine opcode
