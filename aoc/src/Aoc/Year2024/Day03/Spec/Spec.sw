-- Day 3's part 2 as the puzzle states it, over the instructions found in
-- the memory. The proofs (Proofs/) show the program computes it, for every
-- list of instructions.

namespace Aoc.Year2024.Day03.Spec
import Aoc.Year2024.Day03 (..)
import Std (Bool, List, Nat, Option)

-- "The do() instruction enables future mul instructions. The don't()
-- instruction disables future mul instructions."
def setting: Instruction → Option Bool
  | Mul left right => None
  | Do => Some True
  | Dont => Some False

-- "Only the most recent do() or don't() instruction applies. At the
-- beginning of the program, mul instructions are enabled."
def enabledAfter (earlier: List Instruction): Bool :=
  match earlier.filterMap setting |> .last with
    | Some enabled => enabled
    | None => True

-- "Add up all of the results of just the enabled multiplications": each
-- instruction counts when the instructions before it leave `mul` enabled.
def enabledResults (instructions: List Instruction): Nat :=
  instructions.withIndex.sumBy (((index, instruction)) => if enabledAfter (instructions.take index) then instruction.result else 0)

def isDont: Instruction → Bool
  | Dont => True
  | Mul left right => False
  | Do => False
