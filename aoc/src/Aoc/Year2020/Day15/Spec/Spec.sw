--| Day 15 as the puzzle states it: how the starting numbers are written,
--| the numbers spoken turn by turn, and each part's answer. Nothing is
--| shared with the program but `Starting`. The proofs (Proofs/) show the
--| program computes these.

namespace Aoc.Year2020.Day15.Spec
import Aoc.Year2020.Day15 (Starting)
import Std (Char, List, NonEmptyList, Option, Parse)

-- The format

--| A starting number in decimal.
def NumberWritten (read: List Char) (number: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ number = Parse.digitsValue read

--| "Your puzzle input": the starting numbers, separated by commas.
def StartingWritten (read: List Char) (starting: Starting): Prop :=
  Parse.SepBy NumberWritten (read u => read = [',']) read starting.numbers

-- The game

--| How many turns back `number` was last spoken, looking back over `older`
--| (the most recent first): 1 if it was the turn before.
def turnsBack (number: Nat): (older: List Nat) → Option Nat
  | [] => None
  | [spoken, ..older] => if spoken == number then Some 1 else (turnsBack number older).map (turns => turns + 1)

--| "Each turn consists of considering the most recently spoken number: If
--| that was the first time the number has been spoken, the current player
--| says 0. Otherwise, the number had been spoken before; the current player
--| announces how many turns apart the number is from when it was previously
--| spoken." `spoken` is every number spoken so far, the most recent first.
def reply: (spoken: List Nat) → Nat
  | [] => 0
  | [last, ..older] => (turnsBack last older).getOrElse 0

--| The numbers spoken in the first `turns` turns, the most recent first.
--| "They begin by taking turns reading from a list of starting numbers";
--| after that, each turn is the `reply` to the numbers spoken before it.
def spoken (starting: List Nat): (turns: Nat) → List Nat
  | Zero => []
  | Succ turn =>
    let before := spoken starting turn
    let said := if turn < starting.length then starting.getOr turn 0 else reply before
    [said, ..before]

--| The number spoken on `turn` (counting from 1), or 0 if no turn has been taken.
def numberSpoken (starting: List Nat) (turn: Nat): Nat := (spoken starting turn).headOr 0

--| "Given your starting numbers, what will be the 2020th number spoken?"
--| (part 1), and the 30000000th (part 2): `answer` is the number spoken on
--| `turn`.
def Answer (starting: Starting) (turn answer: Nat): Prop := answer = numberSpoken starting.numbers.toList turn
