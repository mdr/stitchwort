-- Day 4, part 2 proved for every grid: the printed answer is the number of
-- rolls the puzzle's rounds remove, as Spec/Spec.sw states it
-- (`part2Correct`, at the bottom). The program's round is the spec's
-- (`roundCells`), so its loop runs the spec's rounds; it stops at the first
-- round that removes no roll, when no roll is accessible, and from then on
-- rounds change nothing (`settleRounds`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Aoc.Day04.Spec (..)
import Std (Bool, Eq, List, Nat, Vec, Void)

-- The rolls the program counts are the spec's.
theorem rollsIsCount (grid: Grid) (rows: Vec (Vec Cell grid.width) grid.height): countRolls rows = rollCount grid (rowsCells rows) :=
  Eq.trans (rollsCells rows)
    (Eq.trans
      (List.sumByCong (r => List.sumBy (c => (rowsCells rows r c).count) (List.range grid.width)) (r => List.sumBy (c => Bool.toNat (rowsCells rows r c == Roll)) (List.range grid.width))
        (List.range grid.height)
        (r => List.sumByCong (c => (rowsCells rows r c).count) (c => Bool.toNat (rowsCells rows r c == Roll)) (List.range grid.width) (c => Eq.sym (isRollCount (rowsCells rows r c)))))
      (Eq.sym (countPositionsSum grid (r c => rowsCells rows r c == Roll))))

-- What a round leaves of a cell with `n` rolls around it: floor if it was
-- an accessible roll.
theorem keepRemove: (a: Cell) -> (n: Nat) -> keep a (n + a.count) = (if a == Roll && n < 4 then Floor else a)
  | Floor, n => rfl
  | Roll, n =>
    match e: Nat.leq 4 n with
      | True =>
        let many: Nat.leq 5 (n + 1) = True := omega
        let notFew: Nat.leq (Succ n) 4 = False := omega
        rewrite many, notFew in rfl
      | False =>
        let notMany: Nat.leq 5 (n + 1) = False := omega
        let few: Nat.leq (Succ n) 4 = True := omega
        rewrite notMany, few in rfl

-- The program's round is the spec's.
theorem roundCells (grid: Grid) (rows: Vec (Vec Cell grid.width) grid.height): Same (rowsCells (roundRows rows)) (removeAccessible grid (rowsCells rows)) :=
  r c =>
    Eq.trans (cellRound rows r c)
      (rewrite windowIsNeighbours grid (rowsCells rows) (rowsCellsBelow rows) (rowsCellsRight rows) r c in
        keepRemove (rowsCells rows r c) (neighbours grid (rowsCells rows) r c))

-- One step of `settleRows`: another round when it removes a roll, else done.
theorem settleMore (rows: Vec (Vec Cell w) h) (fewer: Nat.leq (Succ (countRolls (roundRows rows))) (countRolls rows) = True): settleRows rows = settleRows (roundRows rows) :=
  rewrite settleRows.unfold rows in
  rewrite fewer in
  rfl

theorem settleDone (rows: Vec (Vec Cell w) h) (done: Nat.leq (Succ (countRolls (roundRows rows))) (countRolls rows) = False): settleRows rows = rows :=
  rewrite settleRows.unfold rows in
  rewrite done in
  rfl

-- The loop ends where `fuel` rounds do, for any `fuel` of at least the rolls.
theorem settleRounds (grid: Grid) (rows: Vec (Vec Cell grid.width) grid.height) (fuel: Nat) (enough: countRolls rows <= fuel):
      Same (rowsCells (settleRows rows)) (rounds grid fuel (rowsCells rows))
    decreasing countRolls rows
:=
  let cells := rowsCells rows
  let next := roundRows rows
  let removed := roundCount grid cells
  let same := rollCountSame grid (rowsCells next) (removeAccessible grid cells) (roundCells grid rows)
  let nextRolls := rollsIsCount grid next
  let rowsRolls := rollsIsCount grid rows
  match e: Nat.leq (Succ (countRolls next)) (countRolls rows) with
    | True =>
      let more: fuel = Succ (fuel - 1) := omega
      let stillEnough: countRolls next <= fuel - 1 := omega
      rewrite settleMore rows e, more in
        r c =>
          Eq.trans (settleRounds grid next (fuel - 1) stillEnough [decreasing := e] r c)
            (roundsSame grid (fuel - 1) (rowsCells next) (removeAccessible grid cells) (roundCells grid rows) r c)
    | False =>
      let none: accCount grid cells = 0 := omega [removed, same, nextRolls, rowsRolls]
      rewrite settleDone rows e in
        r c => Eq.sym (roundsFixed grid fuel cells (noneStable grid cells (insideRows grid rows) none) r c)

-- Part 2 is right for every grid: the printed answer is the number of rolls
-- the puzzle's rounds remove.
theorem part2Correct (grid: Grid): solvePart2 grid = part2Spec grid :=
  let cells := cellsOf grid
  let start := rollCount grid cells
  let settled := settleRows grid.rows
  let same := settleRounds grid grid.rows start (omega [rollsIsCount grid grid.rows])
  calc solvePart2 grid
    _ = start - rollCount grid (rowsCells settled)
      := Eq.trans (Eq.cong (t => t - countRolls settled) (rollsIsCount grid grid.rows))
        (Eq.cong (t => start - t) (rollsIsCount grid settled))
    _ = start - rollCount grid (rounds grid start cells) := rewrite rollCountSame grid (rowsCells settled) (rounds grid start cells) same
    _ = part2Spec grid
