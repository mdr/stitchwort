-- Advent of Code 2021, day 12: a map of caves joined by passages, one
-- passage per line (`start-A`). Caves named in capitals are big, the others
-- small. Part 1 counts the paths from `start` to `end` that visit no small
-- cave more than once (big caves as often as they like). Part 2 lets one
-- small cave, other than `start` and `end`, be visited twice.
--
--   $ cd aoc && stitchwort run Aoc.Year2021.Day12.main < inputs/2021/day12.txt
--
-- The puzzle input is committed in aoc/inputs/2021/.
--
-- The program counts the paths by a depth-first search that carries the
-- small caves not yet visited and whether the second visit is still
-- spare. The count is finite only because no passage joins two big caves
-- (two of them could be walked between for ever); the parser checks that.
-- The proofs that both counts are the number of the puzzle's paths are in
-- `Aoc.Year2021.Day12.Proofs` (Proofs/); the tests in
-- `Aoc.Year2021.Day12.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day12
import Std (Bool, Char, DecEq, Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, takeWhile1)

def main(): {IO, Fail} () :=
  let passages := parsePassages IO.readAll()
  IO.print "Part 1: ${solvePart1 passages}"
  IO.print "Part 2: ${solvePart2 passages}"

-- A big cave's name is in capitals: it starts with one ("start" and "end"
-- are small).
def isBig (cave: Text): Bool :=
  match cave.toList with
    | Cons first _ => 65 <= first.toNat && first.toNat <= 90
    | Nil => False

-- One passage per line, `a-b`, each name made of letters; fails unless no
-- passage joins two big caves.
def parsePassages (input: Text): {Fail} (List (Text, Text)) := checkPassages (Parse.eachLine input passage)

def passage(): {Parse} (Text, Text) :=
  let from := takeWhile1 "a cave name" Char.isAsciiLetter
  char '-'
  let to := takeWhile1 "a cave name" Char.isAsciiLetter
  (from, to)

-- The passages, if none joins two big caves; otherwise fail, naming the
-- first that does.
def checkPassages (passages: List (Text, Text)): {Fail} (List (Text, Text)) :=
  match firstBigPair passages with
    | Some (index, (from, to)) => Fail.fail "line ${index + 1}: ${from}-${to} joins two big caves, so there would be no end to the paths"
    | None => passages

-- The first passage between two big caves, with its index.
def firstBigPair (passages: List (Text, Text)): Option (Nat, (Text, Text)) :=
  passages.withIndex.find (((_, (from, to))) => isBig from && isBig to)

-- Every cave named in a passage, each once.
def caves (passages: List (Text, Text)): List Text := passages.flatMap (((from, to)) => [from, to]) |> .distinct

-- The caves a passage leads to from `cave`, each once.
def neighboursOf (passages: List (Text, Text)) (cave: Text): List Text :=
  passages.flatMap (((from, to)) => if from == cave then [to] else if to == cave then [from] else []) |> .distinct

-- Each cave with its neighbours, worked out once.
def neighbourTable (passages: List (Text, Text)): List (Text, List Text) := caves passages |> .map (cave => (cave, neighboursOf passages cave))

def lookupNeighbours (table: List (Text, List Text)) (cave: Text): List Text := table.lookup cave |> .getOrElse []

-- The small caves a path may still visit once it has left `start`.
def smallCaves (passages: List (Text, Text)): List Text :=
  caves passages |> .filter (cave => not (isBig cave || cave == "start" || cave == "end"))

-- How many ways there are on from `cave` to `end`, stepping along `next`:
-- `unvisited` is the small caves not yet visited (`start` and `end` aside),
-- and `spare` whether one of the visited ones may still be visited again.
-- Each step goes to a cave not yet visited (or a big one, or, once, a
-- visited one), so the search ends: the measure is the caves left, then
-- the spare visit, then whether we stand in a small cave. A step between
-- two big caves isn't taken (the parser rules them out).
def pathsOnFrom (next: Text → List Text) (unvisited: List Text) (spare: Bool) (cave: Text): Nat
    decreasing (unvisited.length, 2 * Bool.toNat spare + Bool.toNat (not (isBig cave)))
:=
  next cave |> .sumBy (other =>
    if other == "end" then 1
    else if other == "start" then 0
    else if bigOther: isBig other = True then
      if bigHere: isBig cave = True then 0
      else
        pathsOnFrom next unvisited spare other
          [decreasing := Nat.LexLess.Second rfl (rewrite bigOther, Bool.falseOfNotTrue (isBig cave) bigHere in omega)]
    else if fresh: unvisited.contains other = True then
      pathsOnFrom next (without unvisited other) spare other
        [decreasing := Nat.LexLess.First (withoutShorter unvisited other ((List.memContains unvisited other).forward fresh))]
    else if again: spare = True then
      pathsOnFrom next unvisited False other
        [decreasing := Nat.LexLess.Second rfl (rewrite again, Bool.falseOfNotTrue (isBig other) bigOther in omega)]
    else 0)

-- The caves but `cave`. (A function of its own: a lambda written in the
-- recursive call's argument, inside `sumBy`'s, shows in the termination
-- goal as an unknown `x`.)
def without (caves: List Text) (cave: Text): List Text := caves.filter (c => not (c == cave))

def solvePart1 (passages: List (Text, Text)): Nat :=
  let table := neighbourTable passages
  pathsOnFrom (lookupNeighbours table) (smallCaves passages) False "start"

def solvePart2 (passages: List (Text, Text)): Nat :=
  let table := neighbourTable passages
  pathsOnFrom (lookupNeighbours table) (smallCaves passages) True "start"
