--| Day 12 as the puzzle states it, over the passages as read and the program's
--| `Cave.isBig` (a name in capitals).
--| The proofs (Proofs/) show the program's counts are these answers.

namespace Aoc.Year2021.Day12.Spec
import Aoc.Year2021.Day12 (Cave, Passage, Path)
import Std (List)

--| The passage joins `a` and `b`, either way round: passages go both ways.
def Passage.connects (passage: Passage) (a b: Cave): Bool :=
  (passage.from == a && passage.to == b) || (passage.from == b && passage.to == a)

--| Two caves are connected when a line of the input names them.
def connected (passages: List Passage) (a b: Cave): Bool := passages.any (passage => passage.connects a b)

--| A path goes from cave to cave, each connected to the next...
def Path.follows (path: Path) (passages: List Passage): Bool :=
  path.caves.zipWithNext.all (((from, to)) => connected passages from to)

--| ...from the cave named `start` to the one named `end`.
def Path.startToEnd (path: Path): Bool := path.caves.head == Some Cave.start && path.caves.last == Some Cave.end

--| How many times a path visits a cave.
def Path.visits (path: Path) (cave: Cave): Nat := path.caves.occurrences (c => c == cave)

--| Part 1: big caves may be visited any number of times, small ones at most
--| once.
def SmallOnce (path: Path): Prop := ∀ (cave: Cave) => cave.isBig = False → path.visits cave ≤ 1

def Part1Path (passages: List Passage) (path: Path): Prop :=
  path.startToEnd = True ∧ path.follows passages = True ∧ SmallOnce path

--| Part 2: one small cave may be visited twice and the other small ones at
--| most once (no small cave more than twice, and no two of them more than
--| once each), and `start` and `end` exactly once each.
def OneSmallTwice (path: Path): Prop :=
  (∀ (cave: Cave) => cave.isBig = False → path.visits cave ≤ 2)
    ∧ (∀ (a b: Cave) => a.isBig = False → b.isBig = False → 2 ≤ path.visits a → 2 ≤ path.visits b → a = b)
    ∧ path.visits Cave.start = 1
    ∧ path.visits Cave.end = 1

def Part2Path (passages: List Passage) (path: Path): Prop :=
  path.startToEnd = True ∧ path.follows passages = True ∧ OneSmallTwice path

--| The answer is how many paths there are: `count` of them, listed without
--| repeats, exactly the paths.
def PathCount (isPath: Path → Prop) (count: Nat): Prop :=
  ∃ (paths: List Path) => List.Distinct paths ∧ (∀ (path: Path) => path ∈ paths ↔ isPath path) ∧ paths.length = count

--| What the puzzle leaves unsaid: no passage joins two big caves. Otherwise
--| a path could go back and forth between them for ever, and there would be
--| no number of paths.
def NoBigNeighbours (passages: List Passage): Prop :=
  ∀ (a b: Cave) => connected passages a b = True → a.isBig = True → b.isBig = False
