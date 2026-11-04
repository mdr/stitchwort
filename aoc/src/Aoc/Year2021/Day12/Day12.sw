--| Advent of Code 2021, day 12: a map of caves joined by passages, one
--| passage per line (`start-A`). Caves named in capitals are big, the others
--| small. Part 1 counts the paths from `start` to `end` that visit no small
--| cave more than once (big caves as often as they like). Part 2 lets one
--| small cave, other than `start` and `end`, be visited twice.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day12.main < inputs/2021/day12.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program lists the paths by a depth-first search that carries the
--| small caves not yet visited and whether the second visit is still
--| spare, and counts them. The search goes a bounded number of steps deep,
--| which the proofs show is enough. The count is finite only because no
--| passage joins two big caves (two of them could be walked between for
--| ever); the parser checks that.
--| The proofs that both counts are the number of the puzzle's paths are in
--| `Aoc.Year2021.Day12.Proofs` (Proofs/); the tests in
--| `Aoc.Year2021.Day12.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day12
import Std (Bool, Char, DecEq, Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, takeWhile1)

def main(): {IO, Fail} () :=
  let passages := parsePassages IO.readAll()
  IO.print "Part 1: ${solvePart1 passages}"
  IO.print "Part 2: ${solvePart2 passages}"

--| A big cave's name is in capitals: it starts with one ("start" and "end"
--| are small).
def isBig (cave: Text): Bool :=
  match cave.toList with
    | [first, .._] => 65 <= first.toNat && first.toNat <= 90
    | [] => False

--| One passage per line, `a-b`, each name made of letters; fails unless no
--| passage joins two big caves.
def parsePassages (input: Text): {Fail} List (Text, Text) := checkPassages (Parse.eachLine input passage)

def passage(): {Parse} (Text, Text) :=
  let from := takeWhile1 "a cave name" Char.isAsciiLetter
  char '-'
  let to := takeWhile1 "a cave name" Char.isAsciiLetter
  (from, to)

--| The passages, if none joins two big caves; otherwise fail, naming the
--| first that does.
def checkPassages (passages: List (Text, Text)): {Fail} List (Text, Text) :=
  match firstBigPair passages with
    | Some (index, (from, to)) => Fail.fail "line ${index + 1}: ${from}-${to} joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
    | None => passages

--| The first passage between two big caves, with its index.
def firstBigPair (passages: List (Text, Text)): Option (Nat, (Text, Text)) := passages.withIndex.find (((_, passage)) => joinsBig passage)

def joinsBig (passage: (Text, Text)): Bool := isBig passage.fst && isBig passage.snd

--| Every cave named in a passage, each once.
def caves (passages: List (Text, Text)): List Text := passages.flatMap (((from, to)) => [from, to]) |> .distinct

--| The caves a passage leads to from `cave`, each once.
def neighboursOf (passages: List (Text, Text)) (cave: Text): List Text :=
  passages.flatMap (((from, to)) => if from == cave then [to] else if to == cave then [from] else []) |> .distinct

--| Each cave with its neighbours, worked out once.
def neighbourTable (passages: List (Text, Text)): List (Text, List Text) := caves passages |> .map (cave => (cave, neighboursOf passages cave))

def lookupNeighbours (table: List (Text, List Text)) (cave: Text): List Text := table.lookup cave |> .getOrElse []

--| The small caves a path may still visit once it has left `start`.
def smallCaves (passages: List (Text, Text)): List Text :=
  caves passages |> .filter (cave => not (isBig cave || cave == "start" || cave == "end"))

--| What a step from `cave` to `other` does, given the small caves not yet
--| visited (`start` and `end` aside) and whether one of the visited ones may
--| still be visited again: it reaches the end, isn't allowed, or goes on
--| with the caves then unvisited and the spare visit then left.
type Step =
  | Finish
  | Blocked
  | Continue (unvisited: List Text) (spare: Bool)

def step (unvisited: List Text) (spare: Bool) (cave: Text) (other: Text): Step :=
  if other == "end" then Finish
  else if other == "start" then Blocked
  else if isBig other then (if isBig cave then Blocked else Continue unvisited spare)
  else if unvisited.contains other then Continue (without unvisited other) spare
  else if spare then Continue unvisited False
  else Blocked

--| The caves but `cave`.
def without (caves: List Text) (cave: Text): List Text := caves.filter (c => not (c == cave))

--| The ways on from `cave` to `end`, stepping along `next`, each as the
--| caves after `cave`, in at most `steps` steps.
def routesFrom (next: Text → List Text) (unvisited: List Text) (spare: Bool) (cave: Text): (steps: Nat) → List (List Text)
  | Zero => []
  | Succ more =>
    List.concat (next cave |> .map (other =>
      routesVia other (match step unvisited spare cave other with
        | Finish => [[]]
        | Blocked => []
        | Continue left stillSpare => routesFrom next left stillSpare other more)))

--| The routes on from `other`, with `other` in front.
def routesVia (other: Text) (after: List (List Text)): List (List Text) := after.map (Cons other)

--| How far a search can still go: each step that goes on visits a small
--| cave not visited before, or uses up the spare visit, or leaves a small
--| cave for a big one (never a big one for another), so this goes down by
--| at least 1 (`stepDecreases`), and a route has at most this many steps
--| and one more.
def reach (unvisited: List Text) (spare: Bool) (cave: Text): Nat :=
  3 * unvisited.length + 2 * Bool.toNat spare + Bool.toNat (not (isBig cave))

--| The paths from `start` to `end`: with `spare`, one small cave may be
--| visited twice. Searching `3 * unvisited.length + 4` steps deep is enough
--| (`pathsCorrect`).
def paths (passages: List (Text, Text)) (spare: Bool): List (List Text) :=
  let table := neighbourTable passages
  let unvisited := smallCaves passages
  routesFrom (lookupNeighbours table) unvisited spare "start" (3 * unvisited.length + 4) |> .map (Cons "start")

def solvePart1 (passages: List (Text, Text)): Nat := paths passages (spare := False) |> .length

def solvePart2 (passages: List (Text, Text)): Nat := paths passages (spare := True) |> .length
