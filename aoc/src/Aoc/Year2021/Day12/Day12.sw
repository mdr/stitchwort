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

--| A cave, named by letters: `start`, `end`, a big cave in capitals or a
--| small one.
type Cave = { name: Text }

--| Where every path begins...
def Cave.start: Cave := { name = "start" }

--| ...and ends.
def Cave.end: Cave := { name = "end" }

def Cave.isStart (cave: Cave): Bool := cave == Cave.start

def Cave.isEnd (cave: Cave): Bool := cave == Cave.end

--| A big cave's name is in capitals: it starts with one ("start" and "end"
--| are small).
def Cave.isBig (cave: Cave): Bool := match cave.name.toList with
  | [first, .._] => 65 <= first.toNat <= 90
  | [] => False

def Cave.isSmall (cave: Cave): Bool := not cave.isBig

--| A passage between two caves, walked either way.
type Passage = { from: Cave, to: Cave }

--| Both ends are big caves (the input mustn't have one).
def Passage.joinsBig (passage: Passage): Bool := passage.from.isBig && passage.to.isBig

--| Where the passage leads from `cave`: its other end, if `cave` is an end.
def Passage.leadsTo (passage: Passage) (cave: Cave): List Cave :=
  if passage.from == cave then [passage.to] else if passage.to == cave then [passage.from] else []

--| A path through the caves, from the first to the last.
type Path = { caves: List Cave }

--| The path that leaves `start` and then goes through `rest`.
def Path.fromStart (rest: List Cave): Path := { caves = [Cave.start, ..rest] }

def main(): {IO, Fail} () :=
  let passages := parsePassages IO.readAll()
  IO.print "Part 1: ${solvePart1 passages}"
  IO.print "Part 2: ${solvePart2 passages}"

--| One passage per line, `a-b`, each name made of letters; fails unless no
--| passage joins two big caves.
def parsePassages (input: Text): {Fail} List Passage := checkPassages (Parse.eachLine input passage)

def cave(): {Parse} Cave := { name = takeWhile1 "a cave name" Char.isAsciiLetter }

def passage(): {Parse} Passage :=
  let from := cave()
  char '-'
  let to := cave()
  { from, to }

--| The passages, if none joins two big caves; otherwise fail, naming the
--| first that does.
def checkPassages (passages: List Passage): {Fail} List Passage := match firstBigPair passages with
  | Some (index, passage) => Fail.fail "line ${index + 1}: ${passage.from.name}-${passage.to.name} joins two big caves, so a path could cross it back and forth forever and there would be infinitely many paths"
  | None => passages

--| The first passage between two big caves, with its index.
def firstBigPair (passages: List Passage): Option (Nat, Passage) := passages.withIndex.find (((_, passage)) => passage.joinsBig)

--| Every cave named in a passage, each once.
def caves (passages: List Passage): List Cave := passages.flatMap (passage => [passage.from, passage.to]) |> .unique

--| The caves a passage leads to from `cave`, each once.
def neighboursOf (passages: List Passage) (cave: Cave): List Cave := passages.flatMap (passage => passage.leadsTo cave) |> .unique

--| Each cave with its neighbours, worked out once.
def neighbourTable (passages: List Passage): List (Cave, List Cave) := caves passages |> .map (cave => (cave, neighboursOf passages cave))

def lookupNeighbours (table: List (Cave, List Cave)) (cave: Cave): List Cave := table.lookup cave |> .getOrElse []

--| The small caves a path may still visit once it has left `start`.
def smallCaves (passages: List Passage): List Cave :=
  caves passages |> .filter (cave => cave.isSmall && not cave.isStart && not cave.isEnd)

--| What a step from `cave` to `other` does, given the small caves not yet
--| visited (`start` and `end` aside) and whether one of the visited ones may
--| still be visited again: it reaches the end, isn't allowed, or goes on
--| with the caves then unvisited and the spare visit then left.
type Step =
  | Finish
  | Blocked
  | Continue (unvisited: List Cave) (spare: Bool)

def step (unvisited: List Cave) (spare: Bool) (cave: Cave) (other: Cave): Step :=
  if other.isEnd then Finish
  else if other.isStart then Blocked
  else if other.isBig then (if cave.isBig then Blocked else Continue unvisited spare)
  else if unvisited.contains other then Continue (without unvisited other) spare
  else if spare then Continue unvisited False
  else Blocked

--| The caves but `cave`.
def without (caves: List Cave) (cave: Cave): List Cave := caves.filter (c => not (c == cave))

--| The ways on from `cave` to `end`, stepping along `next`, each as the
--| caves after `cave`, in at most `steps` steps.
def routesFrom (next: Cave → List Cave) (unvisited: List Cave) (spare: Bool) (cave: Cave): (steps: Nat) → List (List Cave)
  | Zero => []
  | Succ more =>
    List.concat (next cave |> .map (other =>
      routesVia other (match step unvisited spare cave other with
        | Finish => [[]]
        | Blocked => []
        | Continue left stillSpare => routesFrom next left stillSpare other more)))

--| The routes on from `other`, with `other` in front.
def routesVia (other: Cave) (after: List (List Cave)): List (List Cave) := after.map (Cons other)

--| How far a search can still go: each step that goes on visits a small
--| cave not visited before, or uses up the spare visit, or leaves a small
--| cave for a big one (never a big one for another), so this goes down by
--| at least 1 (`stepDecreases`), and a route has at most this many steps
--| and one more.
def reach (unvisited: List Cave) (spare: Bool) (cave: Cave): Nat :=
  3 * unvisited.length + 2 * spare.toNat + cave.isSmall.toNat

--| The paths from `start` to `end`: with `spare`, one small cave may be
--| visited twice. Searching `3 * unvisited.length + 4` steps deep is enough
--| (`pathsCorrect`).
def paths (passages: List Passage) (spare: Bool): List Path :=
  let table := neighbourTable passages
  let unvisited := smallCaves passages
  routesFrom (lookupNeighbours table) unvisited spare Cave.start (3 * unvisited.length + 4) |> .map Path.fromStart

def solvePart1 (passages: List Passage): Nat := paths passages (spare := False) |> .length

def solvePart2 (passages: List Passage): Nat := paths passages (spare := True) |> .length
