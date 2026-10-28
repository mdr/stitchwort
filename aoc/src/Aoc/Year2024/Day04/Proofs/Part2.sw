-- Day 4, part 2 proved for every grid: the printed answer is the number of
-- positions at the centre of an X-MAS, as Spec/Spec.sw states it
-- (`part2Correct`, at the bottom).

namespace Aoc.Year2024.Day04.Proofs
import Aoc.Year2024.Day04 (..)
import Aoc.Year2024.Day04.Spec (..)
import Std (Bool, Char, Eq, List, Nat, Option)

-- Three letters, none missing, are M, A and S one way or the other, as the
-- spec says it.
def masLetters (first: Option Char) (second: Option Char) (third: Option Char): Bool :=
  [first, second, third] == [Some 'M', Some 'A', Some 'S'] ∨ [first, second, third] == [Some 'S', Some 'A', Some 'M']

-- The program's MAS test on three letters, present or not.
theorem masOrNone: (first: Option Char) → (second: Option Char) → (third: Option Char) →
    Option.getOrElse (some3 spellsMas first second third) False = masLetters first second third
  | Some x, Some y, Some z => cases
  | _, _, _ => cases

-- Both of two tests, present or not.
theorem bothOrNone: (one: Option Bool) → (other: Option Bool) →
    at2 (x y => Bool.toNat (x ∧ y)) one other = Bool.toNat (Option.getOrElse one False ∧ Option.getOrElse other False)
  | Some x, Some y => rfl
  | Some x, None => cases
  | None, other => rfl

-- `countCrosses` centre by centre, up to any bound at least as long as the
-- row above: centre j + 1 has MAS from column j to j + 2 down to the right,
-- and from j + 2 to j down to the left.
theorem crossesSum (above: List Char) (middle: List Char) (below: List Char) (n: Nat) (h: above.length ≤ n):
    countCrosses above middle below
      = List.sumBy (List.range n) (c =>
        Bool.toNat (masLetters (above.get c) (middle.get (1 + c)) (below.get (2 + c)) ∧ masLetters (above.get (2 + c)) (middle.get (1 + c)) (below.get c))) :=
  let downRight := List.zipWith3 above (middle.drop 1) (below.drop 2) spellsMas
  let downLeft := List.zipWith3 (above.drop 2) (middle.drop 1) below spellsMas
  let short := Nat.leTrans downRight.length above.length n (lengthZipWith3Le spellsMas above (middle.drop 1) (below.drop 2)) h
  calc countCrosses above middle below
    _ = List.sumBy (List.range n) (c => at2 (x y => Bool.toNat (x ∧ y)) (downRight.get c) (downLeft.get c))
      := Eq.trans (List.countSumBy (List.zipWith downRight downLeft (one other => one ∧ other)) (found => found))
        (sumByZipWith (found => Bool.toNat found) (one other => one ∧ other) downRight downLeft n short)
    _ = List.sumBy (List.range n) (c =>
        Bool.toNat (masLetters (above.get c) (middle.get (1 + c)) (below.get (2 + c)) ∧ masLetters (above.get (2 + c)) (middle.get (1 + c)) (below.get c)))
      := rewrite getZipWith3 spellsMas above (middle.drop 1) (below.drop 2) _, getZipWith3 spellsMas (above.drop 2) (middle.drop 1) below _,
        getDrop middle 1 _, getDrop below 2 _, getDrop above 2 _, bothOrNone _ _, masOrNone _ _ _, masOrNone _ _ _ in rfl

-- With an empty row among the three, there are no crosses in them.
theorem crossesEmpty1 (middle: List Char) (below: List Char): countCrosses [] middle below = 0 := rfl

theorem crossesEmpty2 (above: List Char) (below: List Char): countCrosses above [] below = 0 :=
  rewrite zipWith3Nil2 (below.drop 2) spellsMas above in rfl

theorem crossesEmpty3 (above: List Char) (middle: List Char): countCrosses above middle [] = 0 :=
  rewrite zipWith3Nil3 spellsMas above (middle.drop 1) in rfl

-- An X-MAS read from the top-left corner of its 3 by 3 block at row r,
-- column c.
def crossRead (grid: Grid) (r: Nat) (c: Nat): Nat :=
  Bool.toNat (
    masLetters (letterAt grid r c) (letterAt grid (1 + r) (1 + c)) (letterAt grid (2 + r) (2 + c))
      ∧ masLetters (letterAt grid r (2 + c)) (letterAt grid (1 + r) (1 + c)) (letterAt grid (2 + r) c)
  )

-- The program's answer, block by block, past the last row and column by 3.
theorem programCrosses (grid: Grid):
    solvePart2 grid = List.sumBy (List.range (height grid + 3)) (r => List.sumBy (List.range (width grid + 3)) (c => crossRead grid r c)) :=
  let rows := grid.rows
  let tall := height grid + 3
  let wide := width grid + 3
  calc List.sum (List.zipWith3 rows (rows.drop 1) (rows.drop 2) countCrosses)
    _ = List.sumBy (List.range tall) (r => at3 (x y z => countCrosses x y z) (rows.get r) ((rows.drop 1).get r) ((rows.drop 2).get r))
      := sumByZipWith3 (x => x) countCrosses rows (rows.drop 1) (rows.drop 2) tall omega
    _ = List.sumBy (List.range tall) (r => countCrosses (rowOf grid r) (rowOf grid (1 + r)) (rowOf grid (2 + r)))
      := rewrite getDrop rows 1 _, getDrop rows 2 _,
        at3OrElse (x y z => countCrosses x y z) [] [] [] crossesEmpty1 crossesEmpty2 crossesEmpty3 _ _ _,
        <- List.getOrGet rows _ [], <- List.getOrGet rows _ [], <- List.getOrGet rows _ [] in rfl
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => crossRead grid r c))
      := rewrite crossesSum (rowOf grid _) (rowOf grid (1 + _)) (rowOf grid (2 + _)) wide (rowFits grid _) in rfl

-- No letter at the centre, no cross.
theorem crossAtMissing (grid: Grid) (r: Nat) (c: Nat) (missing: letterAt grid r c = None): Bool.toNat (crossAt grid r c) = 0 :=
  rewrite missing in cases

-- No letter at the top-left corner, no cross read from it.
theorem crossReadMissing (grid: Grid) (r: Nat) (c: Nat) (missing: letterAt grid r c = None): crossRead grid r c = 0 :=
  rewrite missing in cases

-- A centre one row and one column on is a block read from its top-left
-- corner.
theorem crossAtCorner (grid: Grid) (r: Nat) (c: Nat): Bool.toNat (crossAt grid (1 + r) (1 + c)) = crossRead grid r c :=
  rewrite Nat.addComm r 1, Nat.addComm c 1 in rfl

-- There is no centre in the first row or column.
theorem crossAtTop (grid: Grid) (c: Nat): Bool.toNat (crossAt grid 0 c) = 0 := cases

theorem crossAtLeft (grid: Grid) (r: Nat): Bool.toNat (crossAt grid r 0) = 0 := cases

-- The spec's count, past the last row and column by 3.
theorem specCrosses (grid: Grid):
    part2Spec grid = List.sumBy (List.range (height grid + 3)) (r => List.sumBy (List.range (width grid + 3)) (c => crossRead grid r c)) :=
  let rows := grid.rows
  let tall := height grid + 3
  let wide := width grid + 3
  let centres := (r: Nat) => List.sumBy (List.range wide) (c => Bool.toNat (crossAt grid r c))
  let blocks := (r: Nat) => List.sumBy (List.range (width grid + 2)) (c => crossRead grid r c)
  let tallSplit: tall = height grid + 2 + 1 := omega
  let wideSplit: wide = width grid + 2 + 1 := omega
  let row := (r: Nat) =>
    calc centres (1 + r)
      _ = List.sumBy (List.range (width grid + 2 + 1)) (c => Bool.toNat (crossAt grid (1 + r) c)) := rewrite wideSplit in rfl
      _ = blocks r := sumShift 1 (c => Bool.toNat (crossAt grid (1 + r) c)) (c => crossRead grid r c) (width grid + 2)
        (c early =>
          let first: c = 0 := omega
          rewrite first in crossAtLeft grid (1 + r))
        (c => crossAtCorner grid r c)
  calc part2Spec grid
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range (rowOf grid r).length) (c => Bool.toNat (crossAt grid r c)))
      := Eq.sym (sumRangeExtend _ rows.length tall omega (r below => rewrite List.getOrPast rows r [] below in rfl))
    _ = List.sumBy (List.range tall) centres
      := List.sumByCong (List.range tall) _ _ (r =>
        Eq.sym (sumRangeExtend _ (rowOf grid r).length wide (rowFits grid r) (c right => crossAtMissing grid r c (List.getPast (rowOf grid r) c right))))
    _ = List.sumBy (List.range (height grid + 2 + 1)) centres := rewrite tallSplit in rfl
    _ = List.sumBy (List.range (height grid + 2)) blocks := sumShift 1 centres blocks (height grid + 2)
      (r early =>
        let first: r = 0 := omega
        rewrite first in sumRangeZero _ wide (c => crossAtTop grid c))
      row
    _ = List.sumBy (List.range (height grid + 2)) (r => List.sumBy (List.range wide) (c => crossRead grid r c))
      := List.sumByCong (List.range (height grid + 2)) _ _ (r =>
        Eq.sym (sumRangeExtend _ (width grid + 2) wide omega (c right => crossReadMissing grid r c (letterRight grid r c omega))))
    _ = List.sumBy (List.range tall) (r => List.sumBy (List.range wide) (c => crossRead grid r c))
      := Eq.sym (sumRangeExtend _ (height grid + 2) tall omega (r below => sumRangeZero _ wide (c => crossReadMissing grid r c (letterBelow grid r c omega))))

-- Part 2 is right for every grid: the printed answer is the number of
-- centres of an X-MAS.
theorem part2Correct (grid: Grid): solvePart2 grid = part2Spec grid :=
  Eq.trans (programCrosses grid) (Eq.sym (specCrosses grid))
