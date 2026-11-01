-- Day 12 as the puzzle states it, over the list of passages as read (each
-- a pair of cave names) and the program's `isBig` (a name in capitals).
-- The proofs (Proofs/) show the program's counts are these answers.

namespace Aoc.Year2021.Day12.Spec
import Aoc.Year2021.Day12 (isBig)
import Std (List)

-- Two caves are connected when a line of the input names them, either way
-- round: passages go both ways.
def connected (passages: List (Text, Text)) (a: Text) (b: Text): Bool :=
  passages.any (((from, to)) => (from == a && to == b) || (from == b && to == a))

-- A path is a list of caves, each connected to the next...
def followsPassages (passages: List (Text, Text)) (path: List Text): Bool :=
  path.zipWithNext.all (((from, to)) => connected passages from to)

-- ...from the cave named `start` to the one named `end`.
def startToEnd (path: List Text): Bool := path.head == Some "start" && path.last == Some "end"

-- How many times a path visits a cave.
def visits (path: List Text) (cave: Text): Nat := path.occurrences (c => c == cave)

-- Part 1: big caves may be visited any number of times, small ones at most
-- once.
def SmallOnce (path: List Text): Prop := (cave: Text) → isBig cave = False → visits path cave ≤ 1

def Part1Path (passages: List (Text, Text)) (path: List Text): Prop :=
  startToEnd path = True ∧ followsPassages passages path = True ∧ SmallOnce path

-- Part 2: one small cave may be visited twice and the other small ones at
-- most once (no small cave more than twice, and no two of them more than
-- once each), and `start` and `end` exactly once each.
def OneSmallTwice (path: List Text): Prop :=
  ((cave: Text) → isBig cave = False → visits path cave ≤ 2)
    ∧ ((a: Text) → (b: Text) → isBig a = False → isBig b = False → 2 ≤ visits path a → 2 ≤ visits path b → a = b)
    ∧ visits path "start" = 1
    ∧ visits path "end" = 1

def Part2Path (passages: List (Text, Text)) (path: List Text): Prop :=
  startToEnd path = True ∧ followsPassages passages path = True ∧ OneSmallTwice path

-- The answer is how many paths there are: `count` of them, listed without
-- repeats, exactly the paths.
def PathCount (isPath: List Text → Prop) (count: Nat): Prop :=
  ∃ (paths: List (List Text)) =>
    List.Distinct paths ∧ ((path: List Text) → path ∈ paths ↔ isPath path) ∧ paths.length = count

-- What the puzzle leaves unsaid: no passage joins two big caves. Otherwise
-- a path could go back and forth between them for ever, and there would
-- be no number of paths.
def NoBigNeighbours (passages: List (Text, Text)): Prop :=
  (a: Text) → (b: Text) → connected passages a b = True → isBig a = True → isBig b = False
