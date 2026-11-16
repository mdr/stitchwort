--| Each step of the program is the puzzle's: for every program and machine,
--| `Machine.step` takes the step `StepMatches` describes (`stepMatches`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (Bool, Eq, Exists, List, Nat, Option)

--| The program's combo operands stand for what the puzzle's do.
theorem comboAgrees ∀ (registers: Registers) (operand: Nat):
    Option.map (Combo.decode operand) registers.value = comboValue registers operand :=
  match operand with
    | 0 => byComputing
    | 1 => byComputing
    | 2 => byComputing
    | 3 => byComputing
    | 4 => byComputing
    | 5 => byComputing
    | 6 => byComputing
    | Succ (Succ (Succ (Succ (Succ (Succ (Succ operand)))))) => byComputing

--| `Nat.xor` is the puzzle's bitwise XOR.
theorem xorBitwise ∀ (x y: Nat): BitwiseXor x y (x.xor y) := i =>
  calc bitSet (x.xor y) i
    _ = Nat.testBit (x.xor y) i := Eq.flipped (Nat.testBitDiv (x.xor y) i)
    _ = Bool.xor (Nat.testBit x i) (Nat.testBit y i) := Nat.testBitXor i x y
    _ = Bool.xor (bitSet x i) (bitSet y i) := rewrite Nat.testBitDiv x i, Nat.testBitDiv y i

--| An instruction with a combo operand, made by `make`, does what `happens`
--| says of the operand's value.
theorem comboStep ∀ (machine: Machine) (operand: Nat) (make: Combo → Instruction)
    (after: Nat → Machine) (printed: Nat → Option Nat)
    (executes: ∀ (combo: Combo) => machine.execute (make combo)
      = Next (after (machine.registers.value combo)) (printed (machine.registers.value combo))):
    WithCombo machine.registers operand
      (match Option.map (Combo.decode operand) make with
        | Some instruction => machine.execute instruction
        | None => Fault)
      (value =>
        (match Option.map (Combo.decode operand) make with
          | Some instruction => machine.execute instruction
          | None => Fault)
          = Next (after value) (printed value)) :=
  let agrees := comboAgrees machine.registers operand
  match found: Combo.decode operand with
    | None => rewrite Eq.flipped agrees
    | Some combo => rewrite Eq.flipped agrees then executes combo

--| Each opcode, with each operand, does what the puzzle says.
theorem executesDecode ∀ (operand: Nat) (machine: Machine) (opcode: Nat):
    Executes opcode operand machine
      (match Instruction.decode opcode operand with
        | Some instruction => machine.execute instruction
        | None => Fault) :=
  match opcode with
    | 0 =>
      comboStep machine operand Adv
        (value => advanced machine { machine.registers | a = machine.registers.a / Nat.pow 2 value })
        (value => None)
        (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo))
    | 1 => Witness (machine.registers.b.xor operand) (Both (xorBitwise machine.registers.b operand) byComputing)
    | 2 =>
      comboStep machine operand Bst
        (value => advanced machine { machine.registers | b = value % 8 })
        (value => None)
        (combo => byComputing)
    | 3 =>
      match zero: machine.registers.a == 0 with
        | True => byComputing
        | False => byComputing
    | 4 =>
      Witness
        (machine.registers.b.xor machine.registers.c)
        (Both (xorBitwise machine.registers.b machine.registers.c) byComputing)
    | 5 =>
      comboStep machine operand Out (value => advanced machine machine.registers) (value => Some (value % 8)) (combo =>
        byComputing)
    | 6 =>
      comboStep machine operand Bdv
        (value => advanced machine { machine.registers | b = machine.registers.a / Nat.pow 2 value })
        (value => None)
        (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo))
    | 7 =>
      comboStep machine operand Cdv
        (value => advanced machine { machine.registers | c = machine.registers.a / Nat.pow 2 value })
        (value => None)
        (combo => rewrite Nat.shiftRightDiv machine.registers.a (machine.registers.value combo))
    | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ opcode))))))) => byComputing

--| Every step the program takes is the puzzle's.
theorem stepMatches ∀ (program: List Nat) (machine: Machine): StepMatches program machine (machine.step program) :=
  match fetched: program.get machine.pointer with
    | None => byComputing
    | Some opcode =>
      match operandFetched: program.get (machine.pointer + 1) with
        | None => byComputing
        | Some operand => executesDecode operand machine opcode
