-- Day 20 as the puzzle states it, over the program's racetrack: which
-- positions are track, and a position's neighbour in each direction
-- (`step`). The proofs (Proofs/) show the program's counts are these, for
-- every racetrack whose S and E are track.
--
-- The puzzle says "there is only a single path from the start to the end".
-- Nothing here assumes it: times are the fastest over all routes, which on
-- a single path are the times along it.

namespace Aoc.Year2024.Day20.Spec
import Aoc.Year2024.Day20 (..)
import Std (And, Exists, Iff, List, Nat, Option, Set)

-- "The map consists of track (.) - including the start (S) and end (E)
-- positions (both of which also count as track) - and walls (#)."
def onTrack (racetrack: Racetrack) (position: Position): Bool := racetrack.track.contains position

-- "it is allowed to move up, down, left, or right; each such move takes 1
-- picosecond": the position one move from `position`; `None` into a wall or
-- off the map.
def moveTo (racetrack: Racetrack) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if onTrack racetrack next then Some next else None
    | None => None

-- Where some moves from `position` end; `None` if one can't be made.
def race (racetrack: Racetrack) (position: Position): List Direction → Option Position
  | Nil => Some position
  | Cons direction rest =>
    match moveTo racetrack position direction with
      | Some next => race racetrack next rest
      | None => None

-- "The goal is to reach the end position as quickly as possible": some
-- moves from `from` reach `to` in `time` picoseconds, and none sooner.
def IsFastest (racetrack: Racetrack) (from: Position) (to: Position) (time: Nat): Prop :=
  (∃ (moves: List Direction) => race racetrack from moves = Some to ∧ moves.length = time)
    ∧ ((moves: List Direction) → race racetrack from moves = Some to → time ≤ moves.length)

-- "Each cheat has a distinct start position (the position where the cheat
-- is activated, just before the first move that is allowed to go through
-- walls) and end position; cheats are uniquely identified by their start
-- position and end position."
type Cheat = { start: Position, end: Position }

-- "This allows the program to pass through walls as if they were regular
-- track": the fewest moves from the cheat's start to its end, through
-- anything, are the rows plus the columns between them.
def cheatTime (cheat: Cheat): Nat :=
  Nat.absDiff cheat.start.row cheat.end.row + Nat.absDiff cheat.start.column cheat.end.column

-- "a program may disable collision for up to 2 picoseconds ... At the end of
-- the cheat, the program must be back on normal track again" (up to
-- `length` picoseconds): it starts where the program is, on track, and ends
-- on track.
def IsCheat (racetrack: Racetrack) (length: Nat) (cheat: Cheat): Prop :=
  onTrack racetrack cheat.start = True ∧ onTrack racetrack cheat.end = True ∧ cheatTime cheat ≤ length

-- "How many cheats would save you at least 100 picoseconds?": the race with
-- the cheat (the fastest to its start, the cheat, then the fastest from its
-- end to E) takes at least `threshold` picoseconds less than the fastest
-- race from S to E without one.
def SavesAtLeast (racetrack: Racetrack) (length: Nat) (threshold: Nat) (cheat: Cheat): Prop :=
  IsCheat racetrack length cheat
    ∧ (∃ (honest: Nat) => ∃ (before: Nat) => ∃ (after: Nat) =>
      IsFastest racetrack racetrack.start racetrack.end honest
        ∧ IsFastest racetrack racetrack.start cheat.start before
        ∧ IsFastest racetrack cheat.end racetrack.end after
        ∧ before + cheatTime cheat + after + threshold ≤ honest)

-- There are `count` such cheats: a list of them, each once, holding every
-- one.
def IsCount (racetrack: Racetrack) (length: Nat) (threshold: Nat) (count: Nat): Prop :=
  ∃ (cheats: List Cheat) =>
    List.Distinct cheats
      ∧ ((cheat: Cheat) → Iff (cheat ∈ cheats) (SavesAtLeast racetrack length threshold cheat))
      ∧ cheats.length = count
