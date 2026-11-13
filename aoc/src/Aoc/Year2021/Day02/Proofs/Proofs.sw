--| Day 2 proved, for every list of commands: both answers are those of the
--| submarine the spec steers one command at a time (Spec/).
-- Each lemma follows the commands from any starting submarine, so that the
-- induction can carry the submarine along; the answers start it at the
-- surface.

namespace Aoc.Year2021.Day02.Proofs
import Aoc.Year2021.Day02 (..)
import Aoc.Year2021.Day02.Spec (..)
import Std (Int, List)

--| Part 1: the horizontal position grows by the sum of the forward moves.
theorem horizontalAfter (start: Submarine) (commands: List Command):
    (commands.foldLeft start Submarine.follow).horizontal = start.horizontal + horizontal commands :=
  match commands with
    | [] => rfl
    | [command, ..rest] =>
      rewrite horizontalAfter (start.follow command) rest, List.sumByCons rest command Command.ahead in cases

--| And the depth by the downs less the ups.
theorem depthAfter (start: Submarine) (commands: List Command):
    (commands.foldLeft start Submarine.follow).depth = start.depth + commands.sumBy Command.down := match commands with
      | [] => omega
      | [command, ..rest] =>
        rewrite depthAfter (start.follow command) rest, List.sumByCons rest command Command.down in cases

def surface: Submarine := { horizontal = 0, depth = 0 }

--| Part 1 is the puzzle's answer, for every list of commands.
theorem part1Correct (commands: List Command): solvePart1 commands = part1 commands :=
  rewrite horizontalAfter surface commands, depthAfter surface commands in ring

--| The program's part 2 depth, one command at a time: the first command is
--| made at the aim it starts with, and the rest at that aim moved by its down.
theorem aimedDepthCons (aim: Int) (command: Command) (rest: List Command):
    aimedDepth aim [command, ..rest] = aim * command.ahead.toInt + aimedDepth (aim + command.down) rest :=
  List.sumCons _ _

--| Part 2: the horizontal position is part 1's.
theorem aimedHorizontalAfter (start: AimedSubmarine) (commands: List Command):
    (commands.foldLeft start AimedSubmarine.follow).horizontal = start.horizontal + horizontal commands :=
  match commands with
    | [] => rfl
    | [command, ..rest] =>
      rewrite aimedHorizontalAfter (start.follow command) rest, List.sumByCons rest command Command.ahead in cases

--| The aim moves as part 1's depth does (the part 2 answer doesn't need this,
--| but it is the program's reading of the aim).
theorem aimAfter (start: AimedSubmarine) (commands: List Command):
    (commands.foldLeft start AimedSubmarine.follow).aim = start.aim + commands.sumBy Command.down := match commands with
      | [] => omega
      | [command, ..rest] =>
        rewrite aimAfter (start.follow command) rest, List.sumByCons rest command Command.down in cases

--| The depth grows by each forward move times the aim it is made at.
theorem aimedDepthAfter (start: AimedSubmarine) (commands: List Command):
    (commands.foldLeft start AimedSubmarine.follow).depth = start.depth + aimedDepth start.aim commands :=
  match commands with
    | [] => omega
    | [command, ..rest] =>
      rewrite aimedDepthAfter (start.follow command) rest, aimedDepthCons start.aim command rest in
      -- `cases` would leave the forward move's `start.aim + 0` as it is: it
      -- doesn't split a record's field (SW-1913).
      match command with
        | Forward _ => rewrite Int.addZero start.aim in omega
        | Down _ => omega
        | Up _ => omega

def aimedSurface: AimedSubmarine := { horizontal = 0, depth = 0, aim = 0 }

--| Part 2 is the puzzle's answer, for every list of commands.
theorem part2Correct (commands: List Command): solvePart2 commands = part2 commands :=
  rewrite aimedHorizontalAfter aimedSurface commands, aimedDepthAfter aimedSurface commands in ring
