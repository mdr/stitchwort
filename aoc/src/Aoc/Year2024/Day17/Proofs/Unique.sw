--| The puzzle's computer is deterministic: a machine has one step
--| (`stepUnique`) and a halting run one output (`haltsUnique`).

namespace Aoc.Year2024.Day17.Proofs
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (..)
import Std (Bool, Eq, Exists, List, Nat, Option, Void)

--| Two numbers that are both the bitwise XOR of `x` and `y` are equal.
theorem xorUnique ∀ (x y first second: Nat)
    (isFirst: BitwiseXor x y first)
    (isSecond: BitwiseXor x y second):
    first = second :=
  Nat.eqOfTestBit first second (i =>
    rewrite Nat.testBitDiv first i, Nat.testBitDiv second i then Eq.trans (isFirst i) (isSecond i).flipped)

--| An instruction with a combo operand takes one step.
theorem comboUnique ∀ (registers: Registers) (operand: Nat) (first second: Step) (target: Nat → Step)
    (isFirst: WithCombo registers operand first (value => first = target value))
    (isSecond: WithCombo registers operand second (value => second = target value)):
    first = second :=
  match found: comboValue registers operand with
    | Some value => Eq.trans isFirst isSecond.flipped
    | None => Eq.trans isFirst isSecond.flipped

theorem executesUnique ∀ (operand: Nat) (machine: Machine) (first second: Step) (opcode: Nat)
    (isFirst: Executes opcode operand machine first)
    (isSecond: Executes opcode operand machine second):
    first = second :=
  match opcode, isFirst, isSecond with
    | 0, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
    | 1, Witness one (Both isOne firstIs), Witness other (Both isOther secondIs) =>
      rewrite firstIs, secondIs, xorUnique machine.registers.b operand one other isOne isOther
    | 2, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
    | 3, isFirst, isSecond =>
      match zero: machine.registers.a == 0 with
        | True => Eq.trans isFirst isSecond.flipped
        | False => Eq.trans isFirst isSecond.flipped
    | 4, Witness one (Both isOne firstIs), Witness other (Both isOther secondIs) =>
      rewrite firstIs, secondIs, xorUnique machine.registers.b machine.registers.c one other isOne isOther
    | 5, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
    | 6, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
    | 7, isFirst, isSecond => comboUnique machine.registers operand first second _ isFirst isSecond
    | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ opcode))))))), isFirst, isSecond =>
      Eq.trans isFirst isSecond.flipped

--| A machine takes one step.
theorem stepUnique ∀ (program: List Nat) (machine: Machine) (first second: Step)
    (isFirst: StepMatches program machine first)
    (isSecond: StepMatches program machine second):
    first = second :=
  match fetched: program.get machine.pointer with
    | None => Eq.trans isFirst isSecond.flipped
    | Some opcode =>
      match operandFetched: program.get (machine.pointer + 1) with
        | None => Eq.trans isFirst isSecond.flipped
        | Some operand => executesUnique operand machine first second opcode isFirst isSecond

--| Telling steps apart.
def isHalt: Step → Bool
  | Halt => True
  | _ => False

def printedOf: Step → Option Nat
  | Next after printed => printed
  | _ => None

def afterOf (otherwise: Machine): Step → Machine
  | Next after printed => after
  | _ => otherwise

theorem haltNotNext ∀ (after: Machine) (printed: Option Nat) (same: Halt = Next after printed): Void :=
  Bool.trueNotFalse (Eq.cong isHalt same)

theorem quietNotPrints ∀ (after other: Machine) (value: Nat) (same: Next after None = Next other (Some value)): Void :=
  Option.noneNotSome value (Eq.cong printedOf same)

--| A halting run has one output.
theorem haltsUnique ∀ (program: List Nat) (machine: Machine) (first second: List Nat)
    (h: Halts program machine first)
    (h1: Halts program machine second):
    first = second :=
  match first, second, h, h1 with
    | [], [], Stops _ stop, Stops _ alsoStop => byComputing
    | [], second, Stops _ stop, Quiet _ after _ move rest =>
      Void.impossible (haltNotNext after None (stepUnique program machine Halt (Next after None) stop move))
    | [], [value, ..output], Stops _ stop, Prints _ after _ _ move rest =>
      Void.impossible
        (haltNotNext after (Some value) (stepUnique program machine Halt (Next after (Some value)) stop move))
    | first, [], Quiet _ after _ move rest, Stops _ stop =>
      Void.impossible (haltNotNext after None (stepUnique program machine Halt (Next after None) stop move))
    | first, second, Quiet _ after _ move rest, Quiet _ other _ alsoMove alsoRest =>
      let same :=
        Eq.cong (afterOf machine) (stepUnique program machine (Next after None) (Next other None) move alsoMove)
      haltsUnique program after first second rest (rewrite Eq.flipped same at alsoRest)
    | first, [value, ..output], Quiet _ after _ move rest, Prints _ other _ _ alsoMove alsoRest =>
      Void.impossible
        (quietNotPrints after other value
          (stepUnique program machine (Next after None) (Next other (Some value)) move alsoMove))
    | [value, ..output], [], Prints _ after _ _ move rest, Stops _ stop =>
      Void.impossible
        (haltNotNext after (Some value) (stepUnique program machine Halt (Next after (Some value)) stop move))
    | [value, ..output], second, Prints _ after _ _ move rest, Quiet _ other _ alsoMove alsoRest =>
      Void.impossible
        (quietNotPrints other after value
          (stepUnique program machine (Next other None) (Next after (Some value)) alsoMove move))
    | [value, ..output], [otherValue, ..otherOutput], Prints _ after _ _ move rest, Prints _ other _ _ alsoMove
          alsoRest =>
      let steps := stepUnique program machine (Next after (Some value)) (Next other (Some otherValue)) move alsoMove
      let sameAfter := Eq.cong (afterOf machine) steps
      let sameValue := Option.someInjective (Eq.cong printedOf steps)
      rewrite sameValue, haltsUnique program after output otherOutput rest (rewrite Eq.flipped sameAfter at alsoRest)
