-- Day 15 proved, for every warehouse and every list of moves:
--
-- Part 1 (Part1.sw): a move never moves a wall (`moveWalls`) or changes the
-- number of boxes (`moveCount`); it keeps the robot off walls and boxes
-- (`moveSeparate`); and every move (`lineExists`) is the puzzle's push of
-- the line of boxes in front of the robot: nothing moves if a wall is past
-- the line (`pushBlocked`), else the robot steps forward and each box of
-- the line moves one step (`pushMoves`).
--
-- Part 2 (Part2.sw, Widen.sw): a blocked move moves nothing
-- (`blockedMovesNothing`), walls never move (`moveAllWideWalls`), and from
-- a widened warehouse where nothing overlaps, after every move the robot
-- is on no wall or box and every box is whole (`part2Whole`).
--
-- Not proved: that part 2 keeps the number of boxes, and that an unblocked
-- part 2 move moves exactly the boxes the puzzle pushes. NOTES-2024.md
-- says why.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (..)
import Std (And, List)

-- Part 1 over all moves, from a warehouse where nothing overlaps.
theorem part1Moves (warehouse: Warehouse) (moves: List Direction) (separate: Separate warehouse):
    And ((warehouse.moveAll moves).walls = warehouse.walls)
      (And (boxCount (warehouse.moveAll moves) = boxCount warehouse) (Separate (warehouse.moveAll moves))) :=
  Both (moveAllWalls warehouse moves) (Both (moveAllCount warehouse moves) (moveAllSeparate warehouse moves separate))
