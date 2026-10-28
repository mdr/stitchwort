-- The puzzle's computer is deterministic: a machine has one step
-- (`stepUnique`) and a halting run one output (`haltsUnique`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (Bool, Eq, Exists, List, Nat, Option, Void)

-- Two numbers that are both the bitwise XOR of `x` and `y` are equal.
theorem xorUnique (x: Nat) (y: Nat) (first: Nat) (second: Nat) (isFirst: BitwiseXor x y first) (isSecond: BitwiseXor x y second): first = second :=
  Nat.eqOfTestBit first second
    (i =>
      rewrite Nat.testBitDiv first i, Nat.testBitDiv second i in
        Eq.trans (isFirst i) (Eq.sym (isSecond i)))

-- An instruction with a combo operand takes one step.
theorem comboUnique (registers: Registers) (operand: Nat) (first: Step) (second: Step) (target: Nat → Step)
    (isFirst: WithCombo registers operand first (value => first = target value))
    (isSecond: WithCombo registers operand second (value => second = target value)): first = second :=
  match found: comboValue registers operand with
    | Some value => Eq.trans isFirst (Eq.sym isSecond)
    | None => Eq.trans isFirst (Eq.sym isSecond)

theorem executesUnique (operand: Nat) (machine: Machine) (first: Step) (second: Step): (opcode: Nat) →
    Executes opcode operand machine first → Executes opcode operand machine second → first = second
  | 0, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
  | 1, Witness one (Both isOne firstIs), Witness other (Both isOther secondIs) =>
    rewrite firstIs, secondIs, xorUnique machine.registers.b operand one other isOne isOther in rfl
  | 2, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
  | 3, isFirst, isSecond =>
    match zero: machine.registers.a == 0 with
      | True => Eq.trans isFirst (Eq.sym isSecond)
      | False => Eq.trans isFirst (Eq.sym isSecond)
  | 4, Witness one (Both isOne firstIs), Witness other (Both isOther secondIs) =>
    rewrite firstIs, secondIs, xorUnique machine.registers.b machine.registers.c one other isOne isOther in rfl
  | 5, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
  | 6, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
  | 7, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ opcode))))))), isFirst, isSecond => Eq.trans isFirst (Eq.sym isSecond)

-- A machine takes one step.
theorem stepUnique (program: List Nat) (machine: Machine) (first: Step) (second: Step)
    (isFirst: StepMatches program machine first) (isSecond: StepMatches program machine second): first = second :=
  match fetched: program.get machine.pointer with
    | None => Eq.trans isFirst (Eq.sym isSecond)
    | Some opcode =>
      match operandFetched: program.get (machine.pointer + 1) with
        | None => Eq.trans isFirst (Eq.sym isSecond)
        | Some operand => executesUnique operand machine first second opcode isFirst isSecond

-- Telling steps apart.
def isHalt: Step → Bool
  | Halt => True
  | _ => False

def printedOf: Step → Option Nat
  | Next after printed => printed
  | _ => None

def afterOf (otherwise: Machine): Step → Machine
  | Next after printed => after
  | _ => otherwise

theorem haltNotNext (after: Machine) (printed: Option Nat) (same: Halt = Next after printed): Void := Bool.trueNotFalse (Eq.cong isHalt same)

theorem quietNotPrints (after: Machine) (other: Machine) (value: Nat) (same: Next after None = Next other (Some value)): Void :=
  Option.noneNotSome value (Eq.cong printedOf same)

-- A halting run has one output.
theorem haltsUnique (program: List Nat): (machine: Machine) → (first: List Nat) → (second: List Nat) →
    Halts program machine first → Halts program machine second → first = second
  | machine, Nil, Nil, Stops _ stop, Stops _ alsoStop => rfl
  | machine, Nil, second, Stops _ stop, Quiet _ after _ move rest =>
    Void.exfalso (haltNotNext after None (stepUnique program machine Halt (Next after None) stop move))
  | machine, Nil, Cons value output, Stops _ stop, Prints _ after _ _ move rest =>
    Void.exfalso (haltNotNext after (Some value) (stepUnique program machine Halt (Next after (Some value)) stop move))
  | machine, first, Nil, Quiet _ after _ move rest, Stops _ stop =>
    Void.exfalso (haltNotNext after None (stepUnique program machine Halt (Next after None) stop move))
  | machine, first, second, Quiet _ after _ move rest, Quiet _ other _ alsoMove alsoRest =>
    let same := Eq.cong (afterOf machine) (stepUnique program machine (Next after None) (Next other None) move alsoMove)
    haltsUnique program after first second rest (rewrite Eq.sym same at alsoRest)
  | machine, first, Cons value output, Quiet _ after _ move rest, Prints _ other _ _ alsoMove alsoRest =>
    Void.exfalso (quietNotPrints after other value (stepUnique program machine (Next after None) (Next other (Some value)) move alsoMove))
  | machine, Cons value output, Nil, Prints _ after _ _ move rest, Stops _ stop =>
    Void.exfalso (haltNotNext after (Some value) (stepUnique program machine Halt (Next after (Some value)) stop move))
  | machine, Cons value output, second, Prints _ after _ _ move rest, Quiet _ other _ alsoMove alsoRest =>
    Void.exfalso (quietNotPrints other after value (stepUnique program machine (Next other None) (Next after (Some value)) alsoMove move))
  | machine, Cons value output, Cons otherValue otherOutput, Prints _ after _ _ move rest, Prints _ other _ _ alsoMove alsoRest =>
    let steps := stepUnique program machine (Next after (Some value)) (Next other (Some otherValue)) move alsoMove
    let sameAfter := Eq.cong (afterOf machine) steps
    let sameValue := Option.someInjective value otherValue (Eq.cong printedOf steps)
    rewrite sameValue, haltsUnique program after output otherOutput rest (rewrite Eq.sym sameAfter at alsoRest) in rfl
