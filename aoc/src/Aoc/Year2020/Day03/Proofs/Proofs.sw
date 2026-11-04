--| Day 3 proved: on every rectangular map, for every slope, the program's
--| count is the trees on the puzzle's path through the repeating map
--| (Spec/), so both answers are the puzzle's.

namespace Aoc.Year2020.Day03.Proofs
import Aoc.Common (Grid, Position, cellAt)
import Aoc.Common.Proofs (lookupOrAt)
import Aoc.Year2020.Day03 (..)
import Aoc.Year2020.Day03.Spec (..)
import Std (Bool, Eq, List, Nat, Option)

theorem modSubSelf (column: Nat) (width: Nat) (nonEmpty: width ≠ 0) (past: width ≤ column): (column - width) % width = column % width :=
  let back: column - width + 1 * width = column := omega
  let shifted := Nat.modAddMul (column - width) 1 width
  rewrite back at shifted in Eq.sym shifted

--| The repeating pattern is the pattern at the column's remainder.
theorem repeatingAtMod (pattern: List Square) (nonEmpty: pattern.length ≠ 0) (column: Nat):
    repeatingAt pattern column = pattern.get (column % pattern.length) decreasing column :=
  if within: column < pattern.length then
    rewrite repeatingAt.eq.ifTrue pattern column within, Nat.modSmall column pattern.length within in rfl
  else
    rewrite repeatingAt.eq.ifFalse.ifTrue pattern column within nonEmpty,
      repeatingAtMod pattern nonEmpty (column - pattern.length) [decreasing := omega],
      modSubSelf column pattern.length nonEmpty omega in rfl

theorem repeatingAtWrap (pattern: List Square) (column: Nat): repeatingAt pattern column = pattern.get (wrap column pattern.length) :=
  match pattern with
    | [] => rewrite repeatingAt.eq.ifFalse.ifFalse [] column omega omega in rfl
    | [square, ..rest] => repeatingAtMod [square, ..rest] omega column

--| The program's lookup at the wrapped column is the repeating map's
--| square.
theorem lookupSquareAt (map: Grid Square) (rectangle: map.Rectangle) (position: Position):
    (map.lookupOr Open ({ row = position.row, column = wrap position.column map.width }) == Tree) = (squareAt map position == Some Tree) :=
  rewrite lookupOrAt map Open ({ row = position.row, column = wrap position.column map.width }) in
    match found: map.rows.get position.row with
      | Some pattern =>
        let long: pattern.length = map.width := rectangle pattern (List.memOfGet map.rows position.row pattern found)
        rewrite repeatingAtWrap pattern position.column, long in cases
      | None => rfl

theorem positionEq (a: Nat) (b: Nat) (c: Nat) (d: Nat) (rows: a = c) (columns: b = d): ({ row = a, column = b }: Position) = { row = c, column = d } :=
  rewrite rows, columns in rfl

--| `path` is the positions `from` plus 1, 2, … steps.
theorem pathRange (slope: Slope): (from: Position) → (steps: Nat) →
    path slope from steps = (List.rangeFrom steps 1).map (step => ({ row = from.row + step * slope.down, column = from.column + step * slope.right }: Position))
  | from, Zero => rfl
  | from, Succ more =>
    rewrite pathRange slope (moved from slope) more, List.mapRangeShift _ more 1 in
      Eq.cong (rest => [moved from slope, ..rest]) (List.mapCong _ _ _ (step => positionEq _ _ _ _ omega omega))

theorem takeWhileMap (f: a → b) (p: b → Bool): (xs: List a) → (xs.map f).takeWhile p = (xs.takeWhile (x => p (f x))).map f
  | [] => rfl
  | [x, ..rest] => rewrite takeWhileMap f p rest in cases

theorem treesOnSpec (map: Grid Square) (rectangle: map.Rectangle) (slope: Slope): treesOn map slope = treesEncountered map slope :=
  rewrite pathRange slope { row = 0, column = 0 } map.height,
    takeWhileMap (step => ({ row = 0 + step * slope.down, column = 0 + step * slope.right }: Position)) (position => position.row < map.height) (List.rangeFrom map.height 1),
    List.lengthFilter, List.countMap in
    List.countCongMem _ _ _ (step m => lookupSquareAt map rectangle { row = step * slope.down, column = step * slope.right })

--| Counting up from `start`, `takeWhile` stops by `cutoff` when nothing from
--| `cutoff` on passes, so any count reaching it gives the same.
theorem takeWhileRangeCutoff (p: Nat → Bool) (cutoff: Nat) (fails: (k: Nat) → cutoff ≤ k → p k = False):
    (n: Nat) → (m: Nat) → (start: Nat) → cutoff ≤ start + n → cutoff ≤ start + m →
    (List.rangeFrom n start).takeWhile p = (List.rangeFrom m start).takeWhile p
  | Zero, Zero, start, reachesN, reachesM => rfl
  | Zero, Succ m, start, reachesN, reachesM => rewrite fails start omega in rfl
  | Succ n, Zero, start, reachesN, reachesM => rewrite fails start omega in rfl
  | Succ n, Succ m, start, reachesN, reachesM =>
    match passes: p start with
      | True => rewrite takeWhileRangeCutoff p cutoff fails n m (Succ start) omega omega in rfl
      | False => rfl

--| The spec's bound loses nothing: on a slope that goes down, more steps
--| than the map has rows visit the same positions.
theorem visitedEnough (map: Grid Square) (slope: Slope) (goesDown: 0 < slope.down) (steps: Nat) (enough: map.height ≤ steps):
    (path slope { row = 0, column = 0 } steps).takeWhile (position => position.row < map.height) = visited map slope :=
  let onPath := (step: Nat) => ({ row = 0 + step * slope.down, column = 0 + step * slope.right }: Position)
  let below: Position → Bool := position => position.row < map.height
  rewrite pathRange slope { row = 0, column = 0 } steps, pathRange slope { row = 0, column = 0 } map.height,
    takeWhileMap onPath below (List.rangeFrom steps 1), takeWhileMap onPath below (List.rangeFrom map.height 1),
    takeWhileRangeCutoff (step => step * slope.down < map.height) map.height
      (k past => Bool.falseOfNotTrue _ (isTrue => omega [Nat.leMulPos k slope.down goesDown])) steps map.height 1 omega omega in rfl

theorem part1Correct (map: Grid Square) (rectangle: map.Rectangle): solvePart1 map = part1Answer map :=
  treesOnSpec map rectangle { right = 3, down = 1 }

theorem part2Correct (map: Grid Square) (rectangle: map.Rectangle): solvePart2 map = part2Answer map :=
  Eq.cong (counts => List.product counts) (List.mapCong slopes (treesOn map) (treesEncountered map) (slope => treesOnSpec map rectangle slope))
