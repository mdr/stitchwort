--| Both answers are the spec's: the program's list of paths holds each path
--| once, and exactly the puzzle's paths, when no passage joins two big
--| caves.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Fail, List, Nat, Option, Result, Void)

--| The search starts in `start`, with every small cave unvisited and the
--| spare visit left in part 2.
theorem tracksStart (passages: List Passage) (twice: Bool): Tracks passages twice (smallCaves passages) twice (Path.fromStart []) :=
  let once := (c: Cave) => (Bool.toNatLeOne (Cave.start == c): (Path.fromStart []).visits c ≤ 1)
  Both
    (c named small notStart notEnd => {
      forward = _ => rewrite differ Cave.start c (same => notStart (Eq.sym same)) in rfl,
      backward = _ =>
        (List.memContains (smallCaves passages) c).backward
          (List.memFilterIntro (caves passages) (cave => cave.isSmall && not cave.isStart && not cave.isEnd) named
            (rewrite small, differ c Cave.start notStart, differ c Cave.end notEnd in rfl))
    })
    (Both rfl
      (Both rfl
        (Both
          (Both (c small => omega [once c])
            (Both (a b smallA smallB twiceA twiceB => Void.exfalso (omega [once a])) (Both (omega) (omega))))
          (Both (part2 => Both part2 (c small => once c)) (part1 => Inl part1)))))

--| The paths the program lists are those from `start` to `end` along the
--| passages that keep the visit rule.
theorem pathsCorrect (passages: List Passage) (promise: NoBigNeighbours passages) (twice: Bool) (path: Path):
    path ∈ paths passages twice ↔ (path.startToEnd = True ∧ path.follows passages = True ∧ Within twice path) := {
  forward = found =>
    Exists.elim (List.memMapElim Path.fromStart path _ found) (rest both =>
      let (Both listed same) := both
      let follows := routesFollow (lookupNeighbours (neighbourTable passages)) (smallCaves passages) twice Cave.start (3 * (smallCaves passages).length + 4) rest listed
      let (Both last (Both along within)) :=
        followsCompletes passages (lookupNeighbours (neighbourTable passages)) (a b member => (tableMem passages a b).forward member) twice
          rest (smallCaves passages) twice Cave.start (Path.fromStart []) (tracksStart passages twice) follows
      rewrite <- same in
        Both
          (match rest with
            | [z, ..more] => rewrite last in rfl)
          (Both along within)),
  backward = both =>
    let (Both ends (Both along within)) := both
    match path with
      | { caves = [first, ..rest] } =>
        let isStart: first = Cave.start := Option.someInjective (DecEq.sound (Bool.andLeft ends))
        let isLast := DecEq.sound (Bool.andRight ends)
        let last: rest.last = Some Cave.end :=
          match rest with
            | [] => Void.exfalso (DecEq.soundFalse Cave.start Cave.end rfl (rewrite <- isStart in Option.someInjective isLast))
            | [z, ..more] => isLast
        let completes: Completes passages twice (Path.fromStart []) Cave.start rest := Both last (rewrite isStart at Both along within)
        let follows :=
          completesFollows passages promise (lookupNeighbours (neighbourTable passages)) (a b joined => (tableMem passages a b).backward joined) twice
            rest (smallCaves passages) twice Cave.start (Path.fromStart []) (tracksStart passages twice) completes
        rewrite isStart in
          List.memMap _ rest
            (followRoutes (lookupNeighbours (neighbourTable passages)) (smallCaves passages) twice Cave.start (3 * (smallCaves passages).length + 4) rest (omega [Bool.toNatLeOne twice]) follows)
            Path.fromStart
}

--| The program lists each path once.
theorem pathsDistinct (passages: List Passage) (twice: Bool): List.Distinct (paths passages twice) :=
  List.distinctMap _
    (routesDistinct (lookupNeighbours (neighbourTable passages)) (tableDistinct passages) (smallCaves passages) twice Cave.start (3 * (smallCaves passages).length + 4))
    Path.fromStart (a b same => Eq.cong (path => path.caves.drop 1) same)

--| Part 1's rule is `Within False`...
theorem withinOnce (path: Path): Within False path ↔ SmallOnce path := {
  forward = within => And.left within,
  backward = once =>
    Both once
      (Both (a b smallA smallB twiceA twiceB => Void.exfalso (omega [once a smallA]))
        (Both (once Cave.start startSmall) (once Cave.end endSmall)))
}

--| A path from `start` to `end` visits both.
theorem endsVisited (path: Path) (ends: path.startToEnd = True): 1 ≤ path.visits Cave.start ∧ 1 ≤ path.visits Cave.end :=
  let isLast := DecEq.sound ends.right
  Both
    (match path.caves with
      | [first, ..rest] =>
        let isStart: first = Cave.start := Option.someInjective (DecEq.sound ends.left)
        visitsMember Cave.start [first, ..rest] (Inl isStart))
    (visitsMember Cave.end path.caves (List.lastMem path.caves Cave.end isLast))

--| ...and part 2's, on a path from `start` to `end`, is `Within True`.
theorem withinTwice (path: Path) (ends: path.startToEnd = True): Within True path ↔ OneSmallTwice path :=
  let (Both startSeen endSeen) := endsVisited path ends
  {
    forward = within =>
      let (Both each (Both once (Both startOnce endOnce))) := within
      Both each (Both once (Both (omega) (omega))),
    backward = rule =>
      let (Both each (Both once (Both startOnce endOnce))) := rule
      Both each (Both once (Both (omega) (omega)))
  }

--| Part 1: the program's answer is the number of paths that visit no small
--| cave twice, when no passage joins two big caves.
theorem part1Correct (passages: List Passage) (promise: NoBigNeighbours passages): PathCount (Part1Path passages) (solvePart1 passages) :=
  Witness (paths passages False)
    (Both (pathsDistinct passages False)
      (Both
        (path => {
          forward = found =>
            let (Both ends (Both along within)) := (pathsCorrect passages promise False path).forward found
            Both ends (Both along ((withinOnce path).forward within)),
          backward = valid =>
            let (Both ends (Both along once)) := valid
            (pathsCorrect passages promise False path).backward (Both ends (Both along ((withinOnce path).backward once)))
        })
        rfl))

--| Part 2: the number of paths that visit one small cave (not `start` or
--| `end`) at most twice and the others at most once.
theorem part2Correct (passages: List Passage) (promise: NoBigNeighbours passages): PathCount (Part2Path passages) (solvePart2 passages) :=
  Witness (paths passages True)
    (Both (pathsDistinct passages True)
      (Both
        (path => {
          forward = found =>
            let (Both ends (Both along within)) := (pathsCorrect passages promise True path).forward found
            Both ends (Both along ((withinTwice path ends).forward within)),
          backward = valid =>
            let (Both ends (Both along rule)) := valid
            (pathsCorrect passages promise True path).backward (Both ends (Both along ((withinTwice path ends).backward rule)))
        })
        rfl))

--| From the input: no hypothesis left, as the parser checks the promise.
theorem part1FromInput (input: Text) (passages: List Passage) (parsed: Fail.toResult (() => parsePassages input) = Ok passages):
    PathCount (Part1Path passages) (solvePart1 passages) :=
  part1Correct passages (parseNoBigNeighbours input passages parsed)

theorem part2FromInput (input: Text) (passages: List Passage) (parsed: Fail.toResult (() => parsePassages input) = Ok passages):
    PathCount (Part2Path passages) (solvePart2 passages) :=
  part2Correct passages (parseNoBigNeighbours input passages parsed)
