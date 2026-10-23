-- Day 7 as the puzzle states it, over the parsed manifold, for the proofs in
-- Proofs/Part1.sw and Proofs/Part2.sw. The timelines are explicit: each is
-- the list of splitters the particle reaches, with the way it goes at each,
-- and part 2 counts them.
--
-- In plain words:
--   - The manifold is the rows below S, each `width` columns wide; row 0 is
--     the one just below S. A row's flag in column c says whether there is
--     a splitter there; past the right edge there is empty space.
--   - "A tachyon beam enters the manifold at the location marked S;
--     tachyon beams always move downward": the particle falls from S into
--     row 0, in S's column.
--   - "Beams pass freely through empty space": a particle falling into a
--     row in a column without a splitter falls on into the row below.
--   - "If a tachyon beam encounters a splitter (^), the beam is stopped;
--     instead, a new tachyon beam continues from the immediate left and
--     from the immediate right of the splitter": at a splitter in column c
--     of row r, time splits. In one timeline the particle goes on down from
--     column c - 1, in the other from column c + 1, falling into row r + 1.
--     Left of column 0 it has left the manifold, and that timeline ends.
--   - Below the last row the particle has left the manifold: one timeline.
--   - Part 2: the number of timelines.
--   - Part 1: "how many times will the beam be split?" The beams are all
--     the ways the particle can go, with those that meet merged ("they are
--     both dumping tachyons into the same place"), so a splitter splits the
--     beam once if any timeline reaches it, and not at all if none does.
--     Count the splitters of the manifold that some timeline reaches.

namespace Aoc.Day07.Spec
import Aoc.Day07 (..)
import Std (Fin, List, Option, Vec)

-- Is there a splitter in column c of a row? Past its end, empty space.
def splitterAt (row: Vec Bool w) (c: Nat): Bool := row.toList.getOr False c

type Turn =
  | Left
  | Right

-- A timeline reaching the splitter at row `row`, column `column`, and the
-- way it goes on from there.
type Hit = { row: Nat, column: Nat, turn: Turn }

-- Every timeline of a particle falling into row r in column c, where `rows`
-- are the rows from row r down: each is the list of the splitters it
-- reaches, in order.
def timelinesFrom (r: Nat) (c: Nat): List (Vec Bool w) -> List (List Hit)
  | Nil => [Nil]
  | Cons row rest =>
    if splitterAt row c then
      List.append
        (match c with
          | Zero => [[{ row = r, column = c, turn = Left }]]
          | Succ b => (timelinesFrom (r + 1) b rest).map (Cons { row = r, column = c, turn = Left }))
        ((timelinesFrom (r + 1) (c + 1) rest).map (Cons { row = r, column = c, turn = Right }))
    else timelinesFrom (r + 1) c rest

-- The timelines of the particle from S.
def timelines (manifold: Manifold): List (List Hit) := timelinesFrom 0 manifold.start.toNat manifold.rows

-- Some timeline reaches the splitter in row r, column c.
def reached (ts: List (List Hit)) (r: Nat) (c: Nat): Bool := ts.any (t => t.any (hit => hit.row == r && hit.column == c))

-- Part 1: the splitters that some timeline reaches.
def part1Spec (manifold: Manifold): Nat :=
  List.range manifold.rows.length |> .sumBy (r => List.range manifold.width |> .count (c => reached (timelines manifold) r c))

-- Part 2: the timelines.
def part2Spec (manifold: Manifold): Nat := (timelines manifold).length
