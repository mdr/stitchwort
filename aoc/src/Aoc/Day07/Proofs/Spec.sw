-- Day 7 as the puzzle states it, for the proofs in Proofs/Part1.sw and
-- Proofs/Part2.sw. The timelines are explicit: each is the list of
-- splitters the particle reaches, with the way it goes at each, and part 2
-- counts them.
--
-- In plain words:
--   - The diagram is the input's lines; row r, column c is the c-th
--     character of line r, or empty space ('.') past its end.
--   - "A tachyon beam enters the manifold at the location marked S;
--     tachyon beams always move downward": the particle falls from S into
--     the row below, in S's column (the first S, reading top to bottom and
--     left to right; with no S there is nothing to answer).
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
--     Count the splitters of the diagram that some timeline reaches.
--
-- Shared with the program: `findStart` (where the first S is) and
-- `gridWidth` (the widest line's length: only a bound on where splitters
-- can be).

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)

-- Column c of a line; empty space past its end.
def charAt (line: Text) (c: Nat): Char := line.toList.getOr '.' c

type Turn =
  | Left
  | Right

-- A timeline reaching the splitter at row `row`, column `column`, and the
-- way it goes on from there.
type Hit = { row: Nat, column: Nat, turn: Turn }

-- Every timeline of a particle falling into row r in column c, where
-- `lines` are the rows from row r down: each is the list of the splitters
-- it reaches, in order.
def timelinesFrom (r: Nat) (c: Nat): List Text -> List (List Hit)
  | Nil            => [Nil]
  | Cons line rest =>
    if charAt line c == '^' then
      List.append
        (match c with
           | Zero   => [[{ row = r, column = c, turn = Left }]]
           | Succ b => (timelinesFrom (r + 1) b rest).map (Cons { row = r, column = c, turn = Left }))
        ((timelinesFrom (r + 1) (c + 1) rest).map (Cons { row = r, column = c, turn = Right }))
    else timelinesFrom (r + 1) c rest

-- The timelines of the particle from S.
def timelines (lines: List Text): Option (List (List Hit)) :=
  (findStart lines).map (((r, c)) => timelinesFrom (r + 1) c (lines.drop (r + 1)))

-- Some timeline reaches the splitter in row r, column c.
def reached (ts: List (List Hit)) (r: Nat) (c: Nat): Bool := ts.any (t => t.any (hit => hit.row == r && hit.column == c))

-- Part 1: the splitters that some timeline reaches.
def part1Spec (lines: List Text): Option Nat :=
  (timelines lines).map (ts => List.range lines.length |> .sumBy (r => List.range (gridWidth lines) |> .count (c => reached ts r c)))

-- Part 2: the timelines.
def part2Spec (lines: List Text): Option Nat := (timelines lines).map List.length

test "spec on the example" := (part1Spec example, part2Spec example) == (Some 21, Some 40)
test "spec at the edges" := (part1Spec ["S.", "^.", ".."], part2Spec ["S.", "^.", ".."], part1Spec [".S", ".^", ".^"], part2Spec [".S", ".^", ".^"]) == (Some 1, Some 2, Some 1, Some 2)
test "spec timelines" :=
  Option.map (ts => ts.map (t => t.map (hit => (hit.row, hit.column, hit.turn == Left)))) (timelines ["..S..", "..^..", ".^.^.", "..^.."])
    == Some [ [(1, 2, True), (2, 1, True)], [(1, 2, True), (2, 1, False), (3, 2, True)], [(1, 2, True), (2, 1, False), (3, 2, False)],
              [(1, 2, False), (2, 3, True), (3, 2, True)], [(1, 2, False), (2, 3, True), (3, 2, False)], [(1, 2, False), (2, 3, False)] ]
test "spec without S" := (part1Spec ["^"], part2Spec ["^"]) == (None, None)
