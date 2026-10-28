-- Day 16 as the puzzle states it, over the program's maze: which tiles are
-- open (`isOpen`), a grid point's neighbour in each direction (`step`) and
-- the quarter turns (`clockwise`, `counterclockwise`). The proofs (Proofs/)
-- show the program's answers are these, for every maze whose S and E are
-- open tiles.

namespace Aoc.Year2024.Day16.Spec
import Aoc.Year2024.Day16 (..)
import Std (And, Exists, Iff, List, Nat, Option, Set)

-- "They can move forward one tile at a time (increasing their score by 1
-- point), but never into a wall (#). They can also rotate clockwise or
-- counterclockwise 90 degrees at a time (increasing their score by 1000
-- points)."
type Move =
  | Forward
  | Clockwise
  | Counterclockwise

def Move.points: Move → Nat
  | Forward => 1
  | Clockwise => 1000
  | Counterclockwise => 1000

-- Where a move leaves the reindeer; `None` for a move into a wall.
def move (maze: Maze) (reindeer: Reindeer): Move → Option Reindeer
  | Forward =>
    match reindeer.position.step reindeer.facing with
      | Some next => if maze.isOpen next then Some ({ reindeer | position = next }) else None
      | None => None
  | Clockwise => Some ({ reindeer | facing = reindeer.facing.clockwise })
  | Counterclockwise => Some ({ reindeer | facing = reindeer.facing.counterclockwise })

-- How the reindeer stands before each move and after the last; `None` if a
-- move runs into a wall.
def follow (maze: Maze) (reindeer: Reindeer): List Move → Option (List Reindeer)
  | Nil => Some [reindeer]
  | Cons first rest =>
    match move maze reindeer first with
      | Some next => follow maze next rest |> .map (Cons reindeer)
      | None => None

def score (moves: List Move): Nat := moves.sumBy Move.points

-- "The Reindeer start on the Start Tile (marked S) facing East".
def startingReindeer (maze: Maze): Reindeer := { position = maze.start, facing = East }

-- A path through the maze: moves from the start, never into a wall, and
-- how the reindeer stands along it, ending on the End Tile.
def IsPath (maze: Maze) (moves: List Move) (standings: List Reindeer): Prop :=
  And (follow maze (startingReindeer maze) moves = Some standings) ((standings.last |> .map (reindeer => reindeer.position)) = Some maze.end)

-- "What is the lowest score a Reindeer could possibly get?": some path
-- scores `best`, and none scores less.
def IsLowestScore (maze: Maze) (best: Nat): Prop :=
  And (Exists (List Move) (moves => Exists (List Reindeer) (standings => And (IsPath maze moves standings) (score moves = best))))
    ((moves: List Move) → (standings: List Reindeer) → IsPath maze moves standings → best ≤ score moves)

-- A tile that is "part of any best path through the maze, including the S
-- and E tiles".
def OnBestPath (maze: Maze) (best: Nat) (tile: Position): Prop :=
  Exists (List Move) (moves =>
    Exists (List Reindeer) (standings =>
      And (IsPath maze moves standings) (And (score moves = best) (tile ∈ standings.map (reindeer => reindeer.position)))))

-- "How many tiles are part of at least one of the best paths through the
-- maze?": `count` tiles, each once.
def CountsBestTiles (maze: Maze) (best: Nat) (count: Nat): Prop :=
  Exists (Set Position) (tiles => And ((tile: Position) → Iff (tiles.contains tile = True) (OnBestPath maze best tile)) (tiles.size = count))
