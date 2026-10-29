-- Day 4, part 1 proved for every grid: the printed answer is the number of
-- positions and directions from which XMAS is spelled, as Spec/Spec.sw
-- states it (`part1Correct`, at the bottom).

namespace Aoc.Year2024.Day04.Proofs
import Aoc.Year2024.Day04 (..)
import Aoc.Year2024.Day04.Spec (..)
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Void)

-- Four letters, none missing, are X, M, A and S in that order.
def readsXmas (first: Option Char) (second: Option Char) (third: Option Char) (fourth: Option Char): Bool :=
  first == Some 'X' ∧ second == Some 'M' ∧ third == Some 'A' ∧ fourth == Some 'S'

-- The letters at four positions, each an offset from row r and column c, read
-- XMAS.
def readsAt (grid: Grid) (r: Nat) (c: Nat) (r0: Nat) (c0: Nat) (r1: Nat) (c1: Nat) (r2: Nat) (c2: Nat) (r3: Nat) (c3: Nat): Nat :=
  Bool.toNat (readsXmas (letterAt grid (r0 + r) (c0 + c)) (letterAt grid (r1 + r) (c1 + c)) (letterAt grid (r2 + r) (c2 + c)) (letterAt grid (r3 + r) (c3 + c)))

-- The program's test on four letters, present or not: XMAS one way, plus XMAS
-- the other way (they can't both hold).
theorem at4Spells (a: Option Char) (b: Option Char) (c: Option Char) (d: Option Char):
    Option.getOrElse (Option.map4 (x y z w => Bool.toNat (spellsXmas x y z w)) a b c d) 0 = Bool.toNat (readsXmas a b c d) + Bool.toNat (readsXmas d c b a) :=
  match a, b, c, d with
    | Some x, Some y, Some z, Some w =>
      rewrite Option.someBeqSome x 'X', Option.someBeqSome x 'S', Option.someBeqSome y 'M', Option.someBeqSome y 'A', Option.someBeqSome z 'A', Option.someBeqSome z 'M', Option.someBeqSome w 'S', Option.someBeqSome w 'X' in
        match isX: x == 'X' with
          | True =>
            let same := DecEq.sound x 'X' isX
            rewrite same in cases
          | False => cases
    | _, _, _, _ => cases

-- `countXmas` index by index, up to any bound at least as long as the first
-- list.
theorem countXmasSum (first: List Char) (second: List Char) (third: List Char) (fourth: List Char) (n: Nat) (h: first.length ≤ n):
    countXmas first second third fourth
      = List.sumBy (List.range n) (j => Option.getOrElse (Option.map4 (x y z w => Bool.toNat (spellsXmas x y z w)) (first.get j) (second.get j) (third.get j) (fourth.get j)) 0) :=
  Eq.trans (List.countSumBy (List.zipWith4 first second third fourth spellsXmas) (found => found))
    (List.sumByZipWith4 (found => Bool.toNat found) spellsXmas first second third fourth n h)

-- Row r of the grid (empty past the last).
def rowOf (grid: Grid) (r: Nat): List Char := grid.rows.getOr r []

-- Across row r: XMAS left to right, and right to left.
theorem acrossSum (grid: Grid) (r: Nat) (n: Nat) (h: (rowOf grid r).length ≤ n):
    countAcross (rowOf grid r) = List.sumBy (List.range n) (c => readsAt grid r c 0 0 0 1 0 2 0 3 + readsAt grid r c 0 3 0 2 0 1 0 0) :=
  let row := rowOf grid r
  rewrite countXmasSum row (row.drop 1) (row.drop 2) (row.drop 3) n h, List.getDrop row 1 _, List.getDrop row 2 _, List.getDrop row 3 _, at4Spells _ _ _ _ in rfl

-- Through rows r to r + 3: XMAS down and up, along the diagonal down to the
-- right both ways, and along the one down to the left both ways.
theorem throughSum (grid: Grid) (r: Nat) (n: Nat) (h: (rowOf grid r).length ≤ n):
    countThrough (rowOf grid r) (rowOf grid (1 + r)) (rowOf grid (2 + r)) (rowOf grid (3 + r))
      = List.sumBy (List.range n) (c => readsAt grid r c 0 0 1 0 2 0 3 0 + readsAt grid r c 3 0 2 0 1 0 0 0)
        + List.sumBy (List.range n) (c => readsAt grid r c 0 0 1 1 2 2 3 3 + readsAt grid r c 3 3 2 2 1 1 0 0)
        + List.sumBy (List.range n) (c => readsAt grid r c 0 3 1 2 2 1 3 0 + readsAt grid r c 3 0 2 1 1 2 0 3) :=
  let first := rowOf grid r
  let second := rowOf grid (1 + r)
  let third := rowOf grid (2 + r)
  let fourth := rowOf grid (3 + r)
  let shortened := Nat.leTrans (first.drop 3).length first.length n (List.lengthDropLe first 3) h
  rewrite countXmasSum first second third fourth n h,
    countXmasSum first (second.drop 1) (third.drop 2) (fourth.drop 3) n h,
    countXmasSum (first.drop 3) (second.drop 2) (third.drop 1) fourth n shortened,
    List.getDrop first 3 _, List.getDrop second 1 _, List.getDrop second 2 _, List.getDrop third 1 _, List.getDrop third 2 _, List.getDrop fourth 3 _,
    at4Spells _ _ _ _ in rfl

-- With an empty row among the four, nothing is found through them.
theorem throughEmpty1 (second: List Char) (third: List Char) (fourth: List Char): countThrough [] second third fourth = 0 := rfl

theorem throughEmpty2 (first: List Char) (third: List Char) (fourth: List Char): countThrough first [] third fourth = 0 :=
  rewrite List.zipWith4NilSecond third fourth spellsXmas first, List.zipWith4NilSecond (third.drop 2) (fourth.drop 3) spellsXmas first,
    List.zipWith4NilSecond (third.drop 1) fourth spellsXmas (first.drop 3) in rfl

theorem throughEmpty3 (first: List Char) (second: List Char) (fourth: List Char): countThrough first second [] fourth = 0 :=
  rewrite List.zipWith4NilThird fourth spellsXmas first second, List.zipWith4NilThird (fourth.drop 3) spellsXmas first (second.drop 1),
    List.zipWith4NilThird fourth spellsXmas (first.drop 3) (second.drop 2) in rfl

theorem throughEmpty4 (first: List Char) (second: List Char) (third: List Char): countThrough first second third [] = 0 :=
  rewrite List.zipWith4NilFourth spellsXmas first second third, List.zipWith4NilFourth spellsXmas first (second.drop 1) (third.drop 2),
    List.zipWith4NilFourth spellsXmas (first.drop 3) (second.drop 2) (third.drop 1) in rfl

-- How many rows, and the longest row's length.
def height (grid: Grid): Nat := grid.rows.length

def width (grid: Grid): Nat := grid.rows.maxLength

-- No row is longer than the width, with room to spare.
theorem rowFits (grid: Grid) (r: Nat): (rowOf grid r).length ≤ width grid + 3 :=
  Nat.leTrans (rowOf grid r).length (width grid) (width grid + 3) (List.lengthLeMaxLength grid.rows r) (Nat.leAddRight (width grid) 3)

-- The count of XMAS read at the same offsets from every position, past the
-- last row and column by 3.
def everywhere (grid: Grid) (r0: Nat) (c0: Nat) (r1: Nat) (c1: Nat) (r2: Nat) (c2: Nat) (r3: Nat) (c3: Nat): Nat :=
  List.sumBy (List.range (height grid + 3)) (r => List.sumBy (List.range (width grid + 3)) (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3))

-- The program's answer, line by line: across both ways, down and up, and the
-- two diagonals both ways.
theorem programLines (grid: Grid):
    solvePart1 grid
      = everywhere grid 0 0 0 1 0 2 0 3 + everywhere grid 0 3 0 2 0 1 0 0
        + (everywhere grid 0 0 1 0 2 0 3 0 + everywhere grid 3 0 2 0 1 0 0 0
          + (everywhere grid 0 0 1 1 2 2 3 3 + everywhere grid 3 3 2 2 1 1 0 0)
          + (everywhere grid 0 3 1 2 2 1 3 0 + everywhere grid 3 0 2 1 1 2 0 3)) :=
  let rows := grid.rows
  let tall := height grid + 3
  let wide := width grid + 3
  let across := calc rows.sumBy countAcross
    _ = List.sumBy (List.range rows.length) (r => countAcross (rowOf grid r)) := List.sumByGetOr rows [] countAcross
    _ = List.sumBy (List.range tall) (r => countAcross (rowOf grid r))
      := Eq.sym (List.sumByRangeExtend _ rows.length tall omega (r below => rewrite List.getOrPast rows r [] below in rfl))
    _ = everywhere grid 0 0 0 1 0 2 0 3 + everywhere grid 0 3 0 2 0 1 0 0
      := Eq.trans (List.sumByCong (List.range tall) _ _ (r => acrossSum grid r wide (rowFits grid r)))
        (List.sumByNestedAdd (List.range tall) (List.range wide) (r c => readsAt grid r c 0 0 0 1 0 2 0 3) (r c => readsAt grid r c 0 3 0 2 0 1 0 0))
  let through := calc List.sum (List.zipWith4 rows (rows.drop 1) (rows.drop 2) (rows.drop 3) countThrough)
    _ = List.sumBy (List.range tall) (r => Option.getOrElse (Option.map4 (x y z w => countThrough x y z w) (rows.get r) ((rows.drop 1).get r) ((rows.drop 2).get r) ((rows.drop 3).get r)) 0)
      := List.sumByZipWith4 (x => x) countThrough rows (rows.drop 1) (rows.drop 2) (rows.drop 3) tall omega
    _ = List.sumBy (List.range tall) (r => countThrough (rowOf grid r) (rowOf grid (1 + r)) (rowOf grid (2 + r)) (rowOf grid (3 + r)))
      := List.sumByCong (List.range tall) _ _ (r =>
        rewrite List.getDrop rows 1 _, List.getDrop rows 2 _, List.getDrop rows 3 _,
          Option.getOrElseMap4 (x y z w => countThrough x y z w) [] [] [] [] 0 throughEmpty1 throughEmpty2 throughEmpty3 throughEmpty4 _ _ _ _,
          <- List.getOrGet rows _ [], <- List.getOrGet rows _ [], <- List.getOrGet rows _ [], <- List.getOrGet rows _ [] in rfl)
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 0 2 0 3 0 + readsAt grid r c 3 0 2 0 1 0 0 0)
        + List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 1 2 2 3 3 + readsAt grid r c 3 3 2 2 1 1 0 0)
        + List.sumBy (List.range wide) (c => readsAt grid r c 0 3 1 2 2 1 3 0 + readsAt grid r c 3 0 2 1 1 2 0 3))
      := List.sumByCong (List.range tall) _ _ (r => throughSum grid r wide (rowFits grid r))
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 0 2 0 3 0 + readsAt grid r c 3 0 2 0 1 0 0 0))
        + List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 1 2 2 3 3 + readsAt grid r c 3 3 2 2 1 1 0 0))
        + List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 3 1 2 2 1 3 0 + readsAt grid r c 3 0 2 1 1 2 0 3))
      := Eq.trans (List.sumByAdd (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 0 2 0 3 0 + readsAt grid r c 3 0 2 0 1 0 0 0) + List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 1 2 2 3 3 + readsAt grid r c 3 3 2 2 1 1 0 0)) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 3 1 2 2 1 3 0 + readsAt grid r c 3 0 2 1 1 2 0 3)))
        (Eq.cong (t => t + List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 3 1 2 2 1 3 0 + readsAt grid r c 3 0 2 1 1 2 0 3))) (List.sumByAdd (List.range tall) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 0 2 0 3 0 + readsAt grid r c 3 0 2 0 1 0 0 0)) (r => List.sumBy (List.range wide) (c => readsAt grid r c 0 0 1 1 2 2 3 3 + readsAt grid r c 3 3 2 2 1 1 0 0))))
    _ = everywhere grid 0 0 1 0 2 0 3 0 + everywhere grid 3 0 2 0 1 0 0 0
        + (everywhere grid 0 0 1 1 2 2 3 3 + everywhere grid 3 3 2 2 1 1 0 0)
        + (everywhere grid 0 3 1 2 2 1 3 0 + everywhere grid 3 0 2 1 1 2 0 3)
      := omega [
        List.sumByNestedAdd (List.range tall) (List.range wide) (r c => readsAt grid r c 0 0 1 0 2 0 3 0) (r c => readsAt grid r c 3 0 2 0 1 0 0 0),
        List.sumByNestedAdd (List.range tall) (List.range wide) (r c => readsAt grid r c 0 0 1 1 2 2 3 3) (r c => readsAt grid r c 3 3 2 2 1 1 0 0),
        List.sumByNestedAdd (List.range tall) (List.range wide) (r c => readsAt grid r c 0 3 1 2 2 1 3 0) (r c => readsAt grid r c 3 0 2 1 1 2 0 3)
      ]
  Eq.trans (rfl: solvePart1 grid = rows.sumBy countAcross + List.sum (List.zipWith4 rows (rows.drop 1) (rows.drop 2) (rows.drop 3) countThrough))
    (omega [across, through])

-- Past the last row, and past the longest row, there are no letters.
theorem letterBelow (grid: Grid) (r: Nat) (c: Nat) (below: height grid ≤ r): letterAt grid r c = None :=
  rewrite List.getOrPast grid.rows r [] below in rfl

theorem letterRight (grid: Grid) (r: Nat) (c: Nat) (right: width grid ≤ c): letterAt grid r c = None :=
  List.getPast (rowOf grid r) c (Nat.leTrans (rowOf grid r).length (width grid) c (List.lengthLeMaxLength grid.rows r) right)

-- Nothing reads XMAS when its first letter is missing.
theorem readsAtMissing (grid: Grid) (r: Nat) (c: Nat) (r0: Nat) (c0: Nat) (r1: Nat) (c1: Nat) (r2: Nat) (c2: Nat) (r3: Nat) (c3: Nat)
    (missing: letterAt grid (r0 + r) (c0 + c) = None): readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3 = 0 :=
  rewrite missing in rfl

-- XMAS from every position in one direction, past the last row and column
-- by 3.
def inDirection (grid: Grid) (direction: Direction): Nat :=
  List.sumBy (List.range (height grid + 3)) (r => List.sumBy (List.range (width grid + 3)) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c direction)))

-- Along one row, a count that is 0 in the first three columns and is
-- `readsAt` three columns on adds up to the `readsAt` count.
theorem columnsShifted (grid: Grid) (r: Nat) (r0: Nat) (c0: Nat) (r1: Nat) (c1: Nat) (r2: Nat) (c2: Nat) (r3: Nat) (c3: Nat) (count: Nat → Nat)
    (early: (c: Nat) → c < 3 → count c = 0) (later: (c: Nat) → count (3 + c) = readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3):
    List.sumBy (List.range (width grid + 3)) count = List.sumBy (List.range (width grid + 3)) (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3) :=
  Eq.trans (List.sumByRangeSkipZeros 3 count (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3) (width grid) early later)
    (Eq.sym (List.sumByRangeExtend (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3) (width grid) (width grid + 3) omega
      (c right => readsAtMissing grid r c r0 c0 r1 c1 r2 c2 r3 c3 (letterRight grid (r0 + r) (c0 + c) omega))))

-- The same for rows: a count that is 0 in the first three rows and is the
-- `readsAt` count three rows on adds up to `everywhere`.
theorem rowsShifted (grid: Grid) (r0: Nat) (c0: Nat) (r1: Nat) (c1: Nat) (r2: Nat) (c2: Nat) (r3: Nat) (c3: Nat) (count: Nat → Nat)
    (early: (r: Nat) → r < 3 → count r = 0)
    (later: (r: Nat) → count (3 + r) = List.sumBy (List.range (width grid + 3)) (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3)):
    List.sumBy (List.range (height grid + 3)) count = everywhere grid r0 c0 r1 c1 r2 c2 r3 c3 :=
  let reads := (r: Nat) => List.sumBy (List.range (width grid + 3)) (c => readsAt grid r c r0 c0 r1 c1 r2 c2 r3 c3)
  Eq.trans (List.sumByRangeSkipZeros 3 count reads (height grid) early later)
    (Eq.sym (List.sumByRangeExtend reads (height grid) (height grid + 3) omega
      (r below => List.sumByRangeZero _ (width grid + 3) (c => readsAtMissing grid r c r0 c0 r1 c1 r2 c2 r3 c3 (letterBelow grid (r0 + r) (c0 + c) omega)))))

-- Left to right.
theorem rightward (grid: Grid): inDirection grid { down = Stay, across = Ahead } = everywhere grid 0 0 0 1 0 2 0 3 :=
  let each := (r: Nat) => (c: Nat) =>
    (cases:
      Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Stay, across = Ahead }) = readsAt grid r c 0 0 0 1 0 2 0 3)
  List.sumByCong (List.range (height grid + 3)) _ _ (r => List.sumByCong (List.range (width grid + 3)) _ _ (each r))

-- Right to left: XMAS read across from its other end, three columns on.
theorem leftward (grid: Grid): inDirection grid { down = Stay, across = Back } = everywhere grid 0 3 0 2 0 1 0 0 :=
  let row := (r: Nat) =>
    columnsShifted grid r 0 3 0 2 0 1 0 0 (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Stay, across = Back }))
      (c early => cases) (c => cases)
  List.sumByCong (List.range (height grid + 3)) _ _ row

-- Top to bottom.
theorem downward (grid: Grid): inDirection grid { down = Ahead, across = Stay } = everywhere grid 0 0 1 0 2 0 3 0 :=
  let each := (r: Nat) => (c: Nat) =>
    (cases:
      Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Ahead, across = Stay }) = readsAt grid r c 0 0 1 0 2 0 3 0)
  List.sumByCong (List.range (height grid + 3)) _ _ (r => List.sumByCong (List.range (width grid + 3)) _ _ (each r))

-- Bottom to top: XMAS read down from its other end, three rows on.
theorem upward (grid: Grid): inDirection grid { down = Back, across = Stay } = everywhere grid 3 0 2 0 1 0 0 0 :=
  let each := (r: Nat) => (c: Nat) =>
    (cases: Bool.toNat (spells ['X', 'M', 'A', 'S'] grid (3 + r) c { down = Back, across = Stay }) = readsAt grid r c 3 0 2 0 1 0 0 0)
  rowsShifted grid 3 0 2 0 1 0 0 0 (r => List.sumBy (List.range (width grid + 3)) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Back, across = Stay })))
    (r early => List.sumByRangeZero _ (width grid + 3) (c => cases))
    (r => List.sumByCong (List.range (width grid + 3)) _ _ (each r))

-- Down to the right.
theorem downRight (grid: Grid): inDirection grid { down = Ahead, across = Ahead } = everywhere grid 0 0 1 1 2 2 3 3 :=
  let each := (r: Nat) => (c: Nat) =>
    (cases:
      Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Ahead, across = Ahead }) = readsAt grid r c 0 0 1 1 2 2 3 3)
  List.sumByCong (List.range (height grid + 3)) _ _ (r => List.sumByCong (List.range (width grid + 3)) _ _ (each r))

-- Up to the left: XMAS read down to the right from its other end, three rows
-- and three columns on.
theorem upLeft (grid: Grid): inDirection grid { down = Back, across = Back } = everywhere grid 3 3 2 2 1 1 0 0 :=
  rowsShifted grid 3 3 2 2 1 1 0 0 (r => List.sumBy (List.range (width grid + 3)) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Back, across = Back })))
    (r early => List.sumByRangeZero _ (width grid + 3) (c => cases))
    (r => columnsShifted grid r 3 3 2 2 1 1 0 0 (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid (3 + r) c { down = Back, across = Back })) (c early => cases) (c => cases))

-- Down to the left: XMAS read up to the right from its other end, three
-- columns on.
theorem downLeft (grid: Grid): inDirection grid { down = Ahead, across = Back } = everywhere grid 0 3 1 2 2 1 3 0 :=
  let row := (r: Nat) =>
    columnsShifted grid r 0 3 1 2 2 1 3 0 (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Ahead, across = Back }))
      (c early => cases) (c => cases)
  List.sumByCong (List.range (height grid + 3)) _ _ row

-- Up to the right: XMAS read down to the left from its other end, three rows
-- on.
theorem upRight (grid: Grid): inDirection grid { down = Back, across = Ahead } = everywhere grid 3 0 2 1 1 2 0 3 :=
  let each := (r: Nat) => (c: Nat) =>
    (cases:
      Bool.toNat (spells ['X', 'M', 'A', 'S'] grid (3 + r) c { down = Back, across = Ahead }) = readsAt grid r c 3 0 2 1 1 2 0 3)
  rowsShifted grid 3 0 2 1 1 2 0 3 (r => List.sumBy (List.range (width grid + 3)) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c { down = Back, across = Ahead })))
    (r early => List.sumByRangeZero _ (width grid + 3) (c => cases))
    (r => List.sumByCong (List.range (width grid + 3)) _ _ (each r))

-- With no letter at a position, XMAS starts there in no direction.
theorem noneFromMissing (grid: Grid) (r: Nat) (c: Nat) (missing: letterAt grid r c = None):
    directions.count (spells ['X', 'M', 'A', 'S'] grid r c) = 0 :=
  rewrite Nat.addZero r, Nat.addZero c, missing in rfl

-- The spec, direction by direction, past the last row and column by 3.
theorem specDirections (grid: Grid):
    part1Spec grid
      = inDirection grid { down = Back, across = Back } + inDirection grid { down = Back, across = Stay }
        + inDirection grid { down = Back, across = Ahead } + inDirection grid { down = Stay, across = Back }
        + inDirection grid { down = Stay, across = Ahead } + inDirection grid { down = Ahead, across = Back }
        + inDirection grid { down = Ahead, across = Stay } + inDirection grid { down = Ahead, across = Ahead } :=
  let rows := grid.rows
  let tall := height grid + 3
  let wide := width grid + 3
  calc part1Spec grid
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range (rowOf grid r).length) (c => directions.count (spells ['X', 'M', 'A', 'S'] grid r c)))
      := Eq.sym (List.sumByRangeExtend _ rows.length tall omega (r below => rewrite List.getOrPast rows r [] below in rfl))
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => directions.count (spells ['X', 'M', 'A', 'S'] grid r c)))
      := List.sumByCong (List.range tall) _ _ (r =>
        Eq.sym (List.sumByRangeExtend _ (rowOf grid r).length wide (rowFits grid r) (c right => noneFromMissing grid r c (List.getPast (rowOf grid r) c right))))
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => List.sumBy directions (direction => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c direction))))
      := List.sumByCong (List.range tall) _ _ (r => List.sumByCong (List.range wide) _ _ (c => List.countSumBy directions (spells ['X', 'M', 'A', 'S'] grid r c)))
    _ = List.sumBy (List.range tall) (r => List.sumBy directions (direction => List.sumBy (List.range wide) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c direction))))
      := List.sumByCong (List.range tall) _ _ (r => List.sumBySwap directions (List.range wide) (c direction => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c direction)))
    _ = List.sumBy directions (inDirection grid)
      := List.sumBySwap directions (List.range tall) (r direction => List.sumBy (List.range wide) (c => Bool.toNat (spells ['X', 'M', 'A', 'S'] grid r c direction)))
    _ = inDirection grid { down = Back, across = Back } + inDirection grid { down = Back, across = Stay }
      + inDirection grid { down = Back, across = Ahead } + inDirection grid { down = Stay, across = Back }
      + inDirection grid { down = Stay, across = Ahead } + inDirection grid { down = Ahead, across = Back }
      + inDirection grid { down = Ahead, across = Stay } + inDirection grid { down = Ahead, across = Ahead }

-- Part 1 is right for every grid: the printed answer is the number of
-- positions and directions from which the letters spell XMAS.
theorem part1Correct (grid: Grid): solvePart1 grid = part1Spec grid :=
  omega [programLines grid, specDirections grid, upLeft grid, upward grid, upRight grid, leftward grid,
    rightward grid, downLeft grid, downward grid, downRight grid]
