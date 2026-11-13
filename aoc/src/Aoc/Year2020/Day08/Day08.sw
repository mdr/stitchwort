--| Advent of Code 2020, day 8: a handheld console's boot code, one
--| instruction a line, each an operation (`acc`, `jmp` or `nop`) and a
--| signed argument: "jmp -4". Part 1 is the accumulator just before any
--| instruction runs a second time; part 2 repairs the one corrupted
--| instruction (a `jmp` that should be a `nop`, or the other way round) so
--| that the program terminates, and gives the accumulator then.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day08.main < inputs/2020/day08.txt
--|
--| The program runs the code from a map of positions to instructions,
--| keeping the set of positions not yet run: a run ends when it would run
--| one again, so it never takes more steps than there are instructions.
--| Part 2 tries each `jmp` and `nop` swapped in turn. The proofs, that the
--| parser reads the puzzle's format and that both answers are the
--| puzzle's, are in `Aoc.Year2020.Day08.Proofs` (Proofs/), and the tests
--| in `Aoc.Year2020.Day08.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day08
import Std (Char, Fail, IO, Int, List, Map, Option, Parse, Set, Text)

def main(): {IO, Fail} () :=
  let program := parseProgram IO.readAll()
  IO.print "Part 1: ${solvePart1 program}"
  IO.print "Part 2: ${solvePart2 program}"

type Operation = | Acc | Jmp | Nop

def Operation.word: (operation: Operation) → Text
  | Acc => "acc"
  | Jmp => "jmp"
  | Nop => "nop"

--| "acc +3": an operation and its argument.
type Instruction = { operation: Operation, argument: Int }

--| The boot code, an instruction a line.
type Program = { instructions: List Instruction }

--| The console as it runs: the position of the instruction it runs next
--| (the first is 0) and the accumulator.
type State = { next: Int, accumulator: Int }

def start: State := { next = 0, accumulator = 0 }

--| How a run of the boot code ends.
type Outcome =
  --| It was about to run an instruction for the second time.
  | Loops (accumulator: Int)
  --| It reached the position just after the last instruction.
  | Terminates (accumulator: Int)
  --| It jumped to some other position outside the code.
  | JumpsAway (accumulator: Int)

def operation(): {Parse} Operation := Parse.pick ([Acc, Jmp, Nop].map (operation => (operation.word, operation)))

--| "+3" or "-99": a sign and a whole number.
def argument(): {Parse} Int := Parse.int()

def instruction(): {Parse} Instruction :=
  let operation := operation()
  Parse.char ' '
  let argument := argument()
  { operation, argument }

def parseProgram (input: Text): {Fail} Program := { instructions = Parse.eachLine input instruction }

def Instruction.execute (instruction: Instruction) (state: State): State := match instruction.operation with
  | Acc => { next = state.next + 1, accumulator = state.accumulator + instruction.argument }
  | Jmp => { state | next = state.next + instruction.argument }
  | Nop => { state | next = state.next + 1 }

--| The boot code by position, for lookup, and how many instructions it has.
type Code = { byPosition: Map Nat Instruction, length: Nat }

def Program.code (program: Program): Code := { byPosition = Map.byPosition program.instructions, length = program.instructions.length }

--| Runs `code` from `state`, where `unvisited` holds the positions of the
--| instructions not run yet. Each step removes one, so the run ends.
def Code.runFrom (code: Code) (unvisited: Set Nat) (state: State): Outcome
    decreasing unvisited.size
:= match state.next.toNatChecked with
  | None => JumpsAway state.accumulator
  | Some position =>
    match code.byPosition.get position with
      | None => if position == code.length then Terminates state.accumulator else JumpsAway state.accumulator
      | Some instruction =>
        if fresh: unvisited.contains position = True then
          Code.runFrom code (unvisited.remove position) (instruction.execute state)
            [decreasing := omega [Set.sizeRemovePresent unvisited position fresh, Set.sizePositive unvisited position fresh]]
        else Loops state.accumulator

def Code.run (code: Code): Outcome := code.runFrom (0 ..< code.length).toSet start

def solvePart1 (program: Program): {Fail} Int := match program.code.run with
  | Loops accumulator => accumulator
  | Terminates accumulator => Fail.fail "the boot code terminates, with the accumulator at ${accumulator}"
  | JumpsAway accumulator => Fail.fail "the boot code jumps outside itself, with the accumulator at ${accumulator}"

--| The accumulator, if the run terminated.
def Outcome.terminated: Outcome → Option Int := match some
  | Terminates accumulator => accumulator

--| The instruction with `jmp` and `nop` swapped, if it is either.
def Instruction.repaired (instruction: Instruction): Option Instruction := match instruction.operation with
  | Acc => None
  | Jmp => Some { instruction | operation = Nop }
  | Nop => Some { instruction | operation = Jmp }

--| The accumulator at the end, if the code terminates with `instruction`
--| at `position` repaired.
def Code.terminatesRepaired (code: Code) (position: Nat) (instruction: Instruction): Option Int :=
  match instruction.repaired with
    | None => None
    | Some repaired => ({ code | byPosition = code.byPosition.insert position repaired }).run.terminated

def solvePart2 (program: Program): {Fail} Int :=
  let code := program.code
  program.instructions.withIndex.findMap (((position, instruction)) => code.terminatesRepaired position instruction)
    |> .orFail "no repair of one jmp or nop makes the boot code terminate"
