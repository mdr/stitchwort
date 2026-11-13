--| Day 5 proved, for every input: both answers are the number of points
--| where at least two lines overlap (Spec/). Part 2's theorem takes as a
--| hypothesis what the puzzle promises, that every line is horizontal,
--| vertical or diagonal at 45 degrees; part 1's needs none, since it takes
--| only the horizontal and vertical lines.

namespace Aoc.Year2021.Day05.Proofs
import Aoc.Common (..)
import Aoc.Year2021.Day05 (..)
import Aoc.Year2021.Day05.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Pair, Void)

--| The answers.

--| Part 1: the program's answer is the number of points where at least two
--| horizontal or vertical lines overlap, for every list of lines.
theorem part1Correct (lines: List Line): Part1Answer lines (solvePart1 lines) :=
  let straight := lines.filter Line.isStraight
  rewrite <- straightLines lines in overlapsCorrect straight (straightShapes lines)

--| Part 2: the program's answer is the number of points where at least two
--| lines overlap, for every list of lines each horizontal, vertical or
--| diagonal at 45 degrees.
theorem part2Correct (lines: List Line) (shapes: lines.all (line => horizontalOrVertical line ∨ diagonal line) = True):
    Part2Answer lines (solvePart2 lines) :=
  overlapsCorrect lines shapes

--| Both parts count the overlaps of their lines.
theorem overlapsCorrect (lines: List Line) (shapes: lines.all (line => horizontalOrVertical line ∨ diagonal line) = True):
    List.NumberWith (overlaps lines) (overlap lines) :=
  List.numberWithCong (overlaps lines) _ (overlap lines) (p => rewrite listedCoveredBy lines shapes p in rfl)
    (countedTwice (lines.flatMap Line.points))

--| The program's straight lines are the spec's horizontal and vertical ones.
theorem straightLines (lines: List Line): lines.filter Line.isStraight = lines.filter horizontalOrVertical := rfl

--| ... and each of them is horizontal or vertical.
theorem straightShapes (lines: List Line):
    (lines.filter Line.isStraight).all (line => horizontalOrVertical line ∨ diagonal line) = True :=
  match lines with
    | [] => rfl
    | [line, ..rest] =>
      match e: Line.isStraight line with
        | True => rewrite straightShapes rest in rewrite e in rfl
        | False => straightShapes rest

-- Counting with a map.

--| The counts of `listed` keep a point when it is listed at least twice.
theorem containsTwice (listed: List Point) (p: Point):
    Map.contains (Map.counts listed |> .filter (_ times => 2 ≤ times)) p = (2 ≤ listed.count (== p)) :=
  rewrite <- Map.getOrCounts p listed in
  match e: Map.get (Map.counts listed) p with
    | None => rewrite Map.getFilter (Map.counts listed) p (_ times => 2 ≤ times), e in rfl
    | Some times => rewrite Map.getFilter (Map.counts listed) p (_ times => 2 ≤ times), e in cases

--| The points listed at least twice in `listed`: the keys of the counts
--| that are at least 2.
theorem countedTwice (listed: List Point):
    List.NumberWith (Map.counts listed |> .count (_ times => 2 ≤ times)) (p => 2 ≤ listed.count (== p)) :=
  let twice := Map.counts listed |> .filter (_ times => 2 ≤ times)
  Witness twice.keys
    (Both (Map.keysDistinct twice)
      (Both (p => rewrite <- containsTwice listed p in Map.memKeys twice p)
        (rewrite <- Map.sizeFilter (Map.counts listed) (_ times => 2 ≤ times) in Eq.sym (Eq.trans (Map.sizeToList twice) (Eq.sym (List.lengthMap (Map.toList twice) Pair.fst))))))

-- Each line's points.

--| A line lists a point once if it covers it, and not at all if it
--| doesn't.
theorem pointsCount (line: Line) (shape: (horizontalOrVertical line ∨ diagonal line) = True) (p: Point):
    line.points.count (== p) = Bool.toNat (covers line p) :=
  match p with
    | point =>
      let steps := Nat.max (Nat.absDiff line.from.x line.to.x) (Nat.absDiff line.from.y line.to.y)
      let k := Nat.max (Nat.absDiff line.from.x point.x) (Nat.absDiff line.from.y point.y)
      Eq.trans (List.countMap (List.range 0 (steps + 1)) (== point) (step => { x = towards line.from.x line.to.x step, y = towards line.from.y line.to.y step }))
        (Eq.trans
          (List.countCongMem _ _ (i => covers line point ∧ i == k)
            (i inRange => pointStep line shape point i (stepInRange steps i inRange)))
          (countRangeOnce (steps + 1) k (covers line point) (c => coveredWithin line point c)))

--| So every line's points, together, list a point once for each line that
--| covers it.
theorem listedCoveredBy (lines: List Line) (shapes: lines.all (line => horizontalOrVertical line ∨ diagonal line) = True) (p: Point):
    (lines.flatMap Line.points).count (== p) = coveredBy lines p :=
  Eq.trans (List.countFlatMap Line.points (== p) lines)
    (Eq.trans
      (List.sumByCongMem lines (line => line.points.count (== p)) (line => Bool.toNat (covers line p))
        (line inLines => pointsCount line (shapes.read line inLines) p))
      (Eq.sym (List.countSumBy lines (line => covers line p))))

--| The step a line takes to reach a point, `k`, is the only one there: the
--| steps `0` to `n - 1` count it once if it is one of them.
theorem countRangeOnce (n: Nat) (k: Nat) (c: Bool) (inRange: (c = True → k < n)): (List.range 0 n).count (i => c ∧ i == k) = c.toNat :=
  match c with
    | False => List.countFalse (List.range 0 n)
    | True => rewrite inRange rfl at List.countRangeEq n k

theorem stepInRange (steps: Nat) (i: Nat) (inRange: i ∈ List.range 0 (steps + 1)): i ≤ steps :=
  let bounds := List.memRangeFrom i (steps + 1) 0 inRange
  omega [And.right bounds]

--| A point a line covers is within its steps.
theorem coveredWithin (line: Line) (point: Point) (c: covers line point = True):
    Nat.max (line.from.x.absDiff point.x) (line.from.y.absDiff point.y) < Nat.max (line.from.x.absDiff line.to.x) (line.from.y.absDiff line.to.y) + 1 :=
  let Both inX (Both inY _) := c
  let bx := betweenBound line.from.x point.x line.to.x inX
  let by := betweenBound line.from.y point.y line.to.y inY
  omega

--| The `i`th point of a line is the point `(x, y)` when the line covers it
--| and it is `k` steps from the first end.
theorem pointStep (line: Line) (shape: (horizontalOrVertical line ∨ diagonal line) = True) (point: Point) (i: Nat)
    (hi: i ≤ Nat.max (line.from.x.absDiff line.to.x) (line.from.y.absDiff line.to.y)):
    (({ x = towards line.from.x line.to.x i, y = towards line.from.y line.to.y i }: Point) == point)
      = (covers line point ∧ i == Nat.max (line.from.x.absDiff point.x) (line.from.y.absDiff point.y)) :=
  Eq.trans (Point.beqMk (towards line.from.x line.to.x i) (towards line.from.y line.to.y i) point)
    (Eq.trans (pointLinear line.from.x line.from.y line.to.x line.to.y i point.x point.y shape hi)
    (Eq.cong (c => c ∧ i == Nat.max (Nat.absDiff line.from.x point.x) (Nat.absDiff line.from.y point.y))
      (Eq.sym (coversLinear line.from.x line.from.y line.to.x line.to.y point.x point.y shape))))

--| A point is another when both coordinates are the same.
theorem Point.beqMk (x: Nat) (y: Nat) (point: Point): (({ x, y }: Point) == point) = (x == point.x ∧ y == point.y) :=
  match point with
    | { x = px, y = py } => rfl

-- One coordinate at a time.

--| Stepping from `a` towards `b`, at most as many steps as they are apart,
--| reaches `x` when `x` is between them and that many steps from `a`.
theorem towardsEq (a: Nat) (b: Nat) (i: Nat) (x: Nat) (h: i ≤ a.absDiff b):
    (towards a b i == x) = (between a x b ∧ i == a.absDiff x) := cases

--| When `a` and `b` are the same, stepping stays put.
theorem towardsFixed (a: Nat) (b: Nat) (i: Nat) (x: Nat) (h: a = b): (towards a b i == x) = between a x b := rewrite h in cases

theorem betweenBound (a: Nat) (x: Nat) (b: Nat) (h: between a x b = True): a.absDiff x ≤ a.absDiff b := cases

theorem betweenFixed (a: Nat) (x: Nat) (b: Nat) (h: a = b) (inside: between a x b = True): a.absDiff x = 0 := rewrite h at inside in cases

theorem absDiffFixed (a: Nat) (b: Nat) (h: a = b): a.absDiff b = 0 := rewrite h in cases

theorem absDiffPositive (a: Nat) (b: Nat) (h: a ≠ b): a.absDiff b ≠ 0 := zero => h (cases)

theorem stepsFixedLeft (a: Nat) (b: Nat) (c: Nat) (i: Nat) (h: a = b) (hi: i ≤ Nat.max (a.absDiff b) c): i ≤ c :=
  rewrite h at hi in cases

theorem stepsFixedRight (a: Nat) (b: Nat) (c: Nat) (i: Nat) (h: a = b) (hi: i ≤ Nat.max c (a.absDiff b)): i ≤ c :=
  rewrite h at hi in cases

theorem stepsDiagonal [d: Nat] [e: Nat] [i: Nat] (h: d = e) (hi: i ≤ Nat.max d e): i ≤ d := rewrite h at hi in cases

theorem diagonalSame (x1: Nat) (x2: Nat) (y1: Nat) (y2: Nat) (h: (x1.absDiff x2 == y1.absDiff y2) = True):
    x1.absDiff x2 = y1.absDiff y2 := cases

-- Both coordinates of a line's points, put together, for each shape of
-- line. `ax` and `ay` are how far the point is across and down from the
-- first end, and `bx` and `by` whether it is between the ends.

theorem combineVertical [ax: Nat] [ay: Nat] (i: Nat) [bx: Bool] [by: Bool] (h: (bx = True → ax = 0)):
    (bx ∧ (by ∧ i == ay)) = ((bx ∧ by ∧ True) ∧ i == Nat.max ax ay) := cases

theorem combineHorizontal [ax: Nat] [ay: Nat] (i: Nat) [bx: Bool] [by: Bool] (h: (by = True → ay = 0)):
    ((bx ∧ i == ax) ∧ by) = ((bx ∧ by ∧ True) ∧ i == Nat.max ax ay) := cases

theorem combineDiagonal [ax: Nat] [ay: Nat] [i: Nat] [d: Nat] (hi: i ≤ d) [bx: Bool] [by: Bool] [e: Bool]
    (h: (bx = True → ax ≤ d)) (h1: (by = True → ay ≤ d)) (h2: (e = True → d = 0)):
    ((bx ∧ i == ax) ∧ (by ∧ i == ay)) = ((bx ∧ by ∧ (e ∨ ax == ay)) ∧ i == Nat.max ax ay) := cases

--| The `i`th point of a horizontal, vertical or diagonal line, as
--| comparisons: it is `(x, y)` when `(x, y)` is in the rectangle the ends
--| span (and, on a diagonal, as far across as down), `i` steps along.
theorem pointLinear (x1: Nat) (y1: Nat) (x2: Nat) (y2: Nat) (i: Nat) (x: Nat) (y: Nat)
    (shape: ((x1 == x2 ∨ y1 == y2) ∨ x1.absDiff x2 == y1.absDiff y2) = True)
    (hi: i ≤ Nat.max (x1.absDiff x2) (y1.absDiff y2)):
    (towards x1 x2 i == x ∧ towards y1 y2 i == y)
      = ((between x1 x x2 ∧ between y1 y y2 ∧ ((x1 == x2 ∨ y1 == y2) ∨ x1.absDiff x == y1.absDiff y)) ∧ i == Nat.max (x1.absDiff x) (y1.absDiff y)) :=
  match vertical: x1 == x2 with
    | True =>
      let hv := vertical.read
      rewrite towardsFixed x1 x2 i x hv, towardsEq y1 y2 i y (stepsFixedLeft x1 x2 _ i hv hi) in
      combineVertical i (betweenFixed x1 x x2 hv)
    | False =>
      match horizontal: y1 == y2 with
        | True =>
          let hh := horizontal.read
          rewrite towardsEq x1 x2 i x (stepsFixedRight y1 y2 _ i hh hi), towardsFixed y1 y2 i y hh in
          combineHorizontal i (betweenFixed y1 y y2 hh)
        | False =>
          let same := diagonalSame x1 x2 y1 y2 shape
          let bounded := stepsDiagonal same hi
          rewrite towardsEq x1 x2 i x bounded, towardsEq y1 y2 i y (rewrite <- same in bounded) in
          combineDiagonal bounded (betweenBound x1 x x2) (h => rewrite same in betweenBound y1 y y2 h)
            (h => Void.exfalso (Bool.falseNotTrue h))

-- The spec's proportion, on these lines.

theorem bothThen [p: Bool] [q: Bool] (bx by: Bool) (h: (bx = True → by = True → p = q)): (bx ∧ by ∧ p) = (bx ∧ by ∧ q) :=
  match bx, by with
    | False, by => rfl
    | True, False => rfl
    | True, True => rewrite h rfl rfl in rfl

theorem productZeroLeft (ax: Nat) (ay: Nat) (dx: Nat) (dy: Nat) (h1: ax = 0) (h2: dx = 0): (ax * dy == ay * dx) = True :=
  rewrite h1, h2, Nat.mulZero ay in rfl

theorem productZeroRight (ax: Nat) (ay: Nat) (dx: Nat) (dy: Nat) (h1: ay = 0) (h2: dy = 0): (ax * dy == ay * dx) = True :=
  rewrite h1, h2, Nat.mulZero ax in rfl

--| On a horizontal or vertical line, every point in the rectangle the ends
--| span is on the line; on a diagonal one, those as far across as down.
theorem coversLinear (x1: Nat) (y1: Nat) (x2: Nat) (y2: Nat) (x: Nat) (y: Nat)
    (shape: ((x1 == x2 ∨ y1 == y2) ∨ x1.absDiff x2 == y1.absDiff y2) = True):
    (between x1 x x2 ∧ between y1 y y2 ∧ x1.absDiff x * y1.absDiff y2 == y1.absDiff y * x1.absDiff x2)
      = (between x1 x x2 ∧ between y1 y y2 ∧ ((x1 == x2 ∨ y1 == y2) ∨ x1.absDiff x == y1.absDiff y)) :=
  bothThen _ _ (bx by =>
    match vertical: x1 == x2 with
      | True =>
        let hv := vertical.read
        rewrite productZeroLeft (Nat.absDiff x1 x) (Nat.absDiff y1 y) (Nat.absDiff x1 x2) (Nat.absDiff y1 y2) (betweenFixed x1 x x2 hv bx) (absDiffFixed x1 x2 hv) in rfl
      | False =>
        match horizontal: y1 == y2 with
          | True =>
            let hh := horizontal.read
            rewrite productZeroRight (Nat.absDiff x1 x) (Nat.absDiff y1 y) (Nat.absDiff x1 x2) (Nat.absDiff y1 y2) (betweenFixed y1 y y2 hh by) (absDiffFixed y1 y2 hh) in rfl
          | False =>
            let same := diagonalSame x1 x2 y1 y2 shape
            rewrite <- same in Nat.mulRightCancelBool (absDiffPositive x1 x2 vertical.read))
