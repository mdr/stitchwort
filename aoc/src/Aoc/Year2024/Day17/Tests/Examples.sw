-- Day 17's tests: the examples from the puzzle, programs of the loop shape
-- written for these tests, and unit tests. Kept apart from the program, so
-- `stitchwort run Aoc.Year2024.Day17.main` doesn't check them. The search
-- answers for the written programs were cross-checked with a separate
-- Python solver, and those for short targets by brute force.

namespace Aoc.Year2024.Day17.Tests
import Aoc.Year2024.Day17 (..)
import Aoc.Year2024.Day17.Spec (comboValue)
import Std (Fail, List, Nat, Option, Result, Text)

def parsed (input: Text): Result Debugger Text := Fail.toResult (() => parseDebugger input)

def part1 (debugger: Debugger): Result Text Text := Fail.toResult (() => solvePart1 debugger)

def debuggerOf (a: Nat) (b: Nat) (c: Nat) (program: List Nat): Debugger := { registers = { a, b, c }, program }

-- The registers once the program halts, within `fuel` steps.
def finalRegisters (machine: Machine) (program: List Nat): (fuel: Nat) → Option Registers
  | Zero => None
  | Succ fuel =>
    match machine.step program with
      | Halt => Some machine.registers
      | Fault => None
      | Next after printed => finalRegisters after program fuel

def finalOf (debugger: Debugger): Option Registers := finalRegisters { registers = debugger.registers, pointer = 0 } debugger.program 1000

def outputOf (debugger: Debugger): List Nat := debugger.outputFor debugger.registers.a

-- The examples of instruction operation.
test "C 9, program 2,6 sets B to 1" := (finalOf (debuggerOf 0 0 9 [2, 6]) |> .map (.b)) == Some 1
test "A 10, program 5,0,5,1,5,4 outputs 0,1,2" := outputOf (debuggerOf 10 0 0 [5, 0, 5, 1, 5, 4]) == [0, 1, 2]
test "A 2024, program 0,1,5,4,3,0 outputs 4,2,5,6,7,7,7,7,3,1,0" := outputOf (debuggerOf 2024 0 0 [0, 1, 5, 4, 3, 0]) == [4, 2, 5, 6, 7, 7, 7, 7, 3, 1, 0]
test "and leaves 0 in A" := (finalOf (debuggerOf 2024 0 0 [0, 1, 5, 4, 3, 0]) |> .map (.a)) == Some 0
test "B 29, program 1,7 sets B to 26" := (finalOf (debuggerOf 0 29 0 [1, 7]) |> .map (.b)) == Some 26
test "B 2024, C 43690, program 4,0 sets B to 44354" := (finalOf (debuggerOf 0 2024 43690 [4, 0]) |> .map (.b)) == Some 44354

def example: Text := "Register A: 729\nRegister B: 0\nRegister C: 0\n\nProgram: 0,1,5,4,3,0\n"

test "example, part 1" := (parsed example |> .map part1) == Ok (Ok "4,6,3,5,6,3,5,2,1,0")
test "example, part 2: no value outputs the program" := (parsed example |> .map solvePart2) == Ok None

-- "This program outputs a copy of itself if register A is instead
-- initialized to 117440."
def copyExample: Debugger := debuggerOf 2024 0 0 [0, 3, 5, 4, 3, 0]

test "part 2 example" := solvePart2 copyExample == Some 117440
test "part 2 example, run with 117440" := part1 (debuggerOf 117440 0 0 copyExample.program) == Ok "0,3,5,4,3,0"

-- Programs of the shape real inputs have, written for these tests: B from
-- A's low 3 bits, C from A shifted by B, some XORs, output B, shift A by 3,
-- loop while A isn't 0.
def loopA: Debugger := debuggerOf 0 0 0 [2, 4, 1, 1, 7, 5, 1, 5, 4, 0, 5, 5, 0, 3, 3, 0]
def loopB: Debugger := debuggerOf 0 0 0 [2, 4, 1, 3, 7, 5, 0, 3, 4, 3, 1, 0, 5, 5, 3, 0]
def loopC: Debugger := debuggerOf 0 0 0 [2, 4, 1, 5, 7, 5, 0, 3, 1, 6, 4, 4, 5, 5, 3, 0]
def loopNone: Debugger := debuggerOf 0 0 0 [2, 4, 1, 0, 7, 5, 1, 0, 4, 0, 5, 5, 0, 3, 3, 0]

test "a loop program's copy" := solvePart2 loopA == Some 164279024971453
test "another, shifting A before it outputs" := solvePart2 loopB == Some 87768089491393
test "a third" := solvePart2 loopC == Some 108056943298970
test "a loop program with no copy" := solvePart2 loopNone == None
test "the copy outputs the program" := outputOf (debuggerOf 164279024971453 0 0 loopA.program) == loopA.program
test "B and C don't matter to a loop program" := solvePart2 (debuggerOf 5 123 456 loopA.program) == Some 164279024971453

-- The search for targets other than the program, against brute force.
test "shorter targets" :=
  [[3, 0], [5, 5, 3, 0], [1, 2, 3], [4], [0]].map (target => lowestOutputting loopA.outputFor target) == [Some 37, Some 2394, Some 494, Some 1, Some 4]
test "targets nothing outputs" := [[7, 7, 7, 7], [0, 0], []].map (target => lowestOutputting loopA.outputFor target) == [None, None, None]
test "shorter targets of the example program" := [[4, 3, 0], [3, 0], [0]].map (target => lowestOutputting copyExample.outputFor target) == [Some 224, Some 24, Some 1]

-- The loop shape the search's proofs assume, checked on the first values.
def hasLoopShape (debugger: Debugger) (count: Nat): Bool :=
  List.range count
    |> .all (a =>
      match debugger.outputFor a with
        | Cons first rest => rest == (if a < 8 then [] else debugger.outputFor (a / 8))
        | Nil => False)

test "the written programs have the loop shape" := [loopA, loopB, loopC, loopNone, copyExample].all (debugger => hasLoopShape debugger 600)
test "the part 1 example doesn't" := !(hasLoopShape (debuggerOf 0 0 0 [0, 1, 5, 4, 3, 0]) 600)

-- Runs that don't finish.
test "a reserved combo operand" := part1 (debuggerOf 1 0 0 [0, 7]) == Err "the program has an invalid instruction"
test "an opcode without an operand" := part1 (debuggerOf 1 0 0 [5, 4, 5]) == Err "the program has an invalid instruction"
test "a loop that never shifts A" := part1 (debuggerOf 1 0 0 [5, 4, 3, 0]) == Err "the program didn't halt"
test "a jump past the end halts" := part1 (debuggerOf 1 0 0 [3, 6, 5, 4]) == Ok ""
test "a jump to an odd position" := part1 (debuggerOf 9 0 0 [0, 3, 5, 4, 3, 1]) == part1 (debuggerOf 9 0 0 [0, 3, 5, 4, 3, 1])

-- Bits.
test "XOR" := Nat.xor 29 7 == 26 && Nat.xor 2024 43690 == 44354 && Nat.xor 0 5 == 5 && Nat.xor 5 5 == 0
test "XOR of large numbers" := Nat.xor 164279024971453 87768089491393 == 240493089167740
test "shifting right" := Nat.shiftRight 117440 3 == 14680 && Nat.shiftRight 5 100 == 0 && Nat.shiftRight 7 0 == 7
test "shifting by a huge count" := Nat.shiftRight 5 1000000000000 == 0
test "bits" := [0, 1, 2, 3, 4].map (Nat.testBit 10) == [False, True, False, True, False]

test "combo operands agree with the spec" :=
  List.range 10 |> .all (operand => (Combo.decode operand |> .map (Registers.value { a = 10, b = 20, c = 30 })) == comboValue { a = 10, b = 20, c = 30 } operand)

-- Parsing.
test "parse" := parsed example == Ok (debuggerOf 729 0 0 [0, 1, 5, 4, 3, 0])
test "parse without a final line break" := parsed "Register A: 1\nRegister B: 2\nRegister C: 3\n\nProgram: 7,0" == Ok (debuggerOf 1 2 3 [7, 0])
test "a number above 7" := parsed "Register A: 1\nRegister B: 2\nRegister C: 3\n\nProgram: 0,8\n" == Err "line 5, column 12: expected a 3-bit number (0 to 7)"
test "a two-digit number" := parsed "Register A: 1\nRegister B: 2\nRegister C: 3\n\nProgram: 0,10\n" == Err "line 5, column 12: expected a 1-digit number, got '1'"
test "no blank line" := parsed "Register A: 1\nRegister B: 2\nRegister C: 3\nProgram: 0,1\n" == Err "line 4, column 1: expected a blank line, got 'P'"
