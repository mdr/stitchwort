-- What both parts' proofs share: the 3 by 3 window around a position, what
-- the program's `peelRow` does to a cell (`peelRowCells`), what a round does
-- to a cell (`cellRound`), and that the window is the spec's neighbours plus
-- the cell itself (`windowIsNeighbours`).

namespace Aoc.Year2025.Day04.Proofs
import Aoc.Year2025.Day04 (..)
import Aoc.Year2025.Day04.Spec (..)
import Std (And, Bool, DecEq, Eq, List, Nat, Vec, Void)

-- Rows of any size as cells by position, as `cellsOf` reads a grid's.
def rowsCells (rows: Vec (Vec Cell w) h): Cells :=
  r c => rows |> Vec.getOr r (Vec.replicate w Floor) |> Vec.getOr c Floor

-- The cells counted from 1, with an empty border: row 0 and column 0 are floor.
def bord (cells: Cells): Nat → Nat → Cell
  | Zero, c => Floor
  | Succ r, Zero => Floor
  | Succ r, Succ c => cells r c

-- The rolls in column c of rows r, r + 1 and r + 2 (all counted from 1).
def colSum (cells: Cells) (r: Nat) (c: Nat): Nat :=
  (bord cells r c).count + (bord cells (Succ r) c).count + (bord cells (Succ (Succ r)) c).count

-- The rolls in the 3 by 3 block around position (r, c) (counted from 0),
-- itself included.
def window (cells: Cells) (r: Nat) (c: Nat): Nat := colSum cells r c + colSum cells r (Succ c) + colSum cells r (Succ (Succ c))

-- What a round leaves in a cell holding `cell`, whose window holds `window`
-- rolls.
def keep (cell: Cell) (window: Nat): Cell := if cell == Roll ∧ 5 ≤ window then Roll else Floor

-- A round never adds a roll.
theorem keepLe: (a: Cell) → (w: Nat) → Cell.count (keep a w) ≤ Cell.count a
  | Floor, w => rfl
  | Roll, w =>
    match Nat.leq 5 w with
      | True => rfl
      | False => rfl

-- What a round leaves of a cell with `n` rolls around it: floor if it was
-- an accessible roll.
theorem keepRemove: (a: Cell) → (n: Nat) → keep a (n + a.count) = (if a == Roll ∧ n < 4 then Floor else a)
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

-- The rolls in column j (counted from 1) of three rows.
def tri (a: Vec Cell w) (x: Vec Cell w) (b: Vec Cell w) (j: Nat): Nat :=
  (Vec.getOr (VCons Floor a) j Floor).count + (Vec.getOr (VCons Floor x) j Floor).count + (Vec.getOr (VCons Floor b) j Floor).count

-- The column sums `peelRow` adds up, counted from 1.
theorem colsAt (a: Vec Cell w) (x: Vec Cell w) (b: Vec Cell w): (j: Nat) →
    Vec.getOr (VCons 0 (Vec.zipWith3 a x b (p q s => Cell.count p + Cell.count q + Cell.count s))) j 0 = tri a x b j
  | Zero => rfl
  | Succ i => Vec.getOrZipWith3 (p q s => Cell.count p + Cell.count q + Cell.count s) Floor Floor Floor 0 rfl a x b i

-- Row v is row r (counted from 1) of `cells`, cell by cell, border included.
def RowIs (cells: Cells) (r: Nat) (v: Vec Cell w): Prop := (j: Nat) → Vec.getOr (VCons Floor v) j Floor = bord cells r j

theorem triCol (cells: Cells) (r: Nat) (a: Vec Cell w) (x: Vec Cell w) (b: Vec Cell w)
    (ha: RowIs cells r a) (hx: RowIs cells (Succ r) x) (hb: RowIs cells (Succ (Succ r)) b) (j: Nat):
    tri a x b j = colSum cells r j :=
  rewrite ha j, hx j, hb j

-- One cell of a peeled row, given the rows above, at and below it.
theorem peelRowCells (cells: Cells) (r: Nat) (c: Nat) (a: Vec Cell w) (x: Vec Cell w) (b: Vec Cell w)
    (ha: RowIs cells r a) (hx: RowIs cells (Succ r) x) (hb: RowIs cells (Succ (Succ r)) b):
    Vec.getOr (peelRow a x b) c Floor = keep (cells r c) (window cells r c) :=
  let cols := Vec.zipWith3 a x b (p q s => Cell.count p + Cell.count q + Cell.count s)
  let add3 := (l: Nat) => (m: Nat) => (n: Nat) => l + m + n
  match e: Nat.leq (Succ c) w with
    | True =>
      calc Vec.getOr (peelRow a x b) c Floor
        _ = keep (Vec.getOr x c Floor) (Vec.getOr (VCons 0 cols) c 0 + Vec.getOr (VCons 0 cols) (Succ c) 0 + Vec.getOr (VCons 0 cols) (Succ (Succ c)) 0)
          := Eq.trans (Vec.getOrZipWith keep Floor 0 Floor rfl x (Vec.around cols 0 add3) c) (rewrite Vec.getOrAround cols c 0 0 e add3)
        _ = keep (Vec.getOr (VCons Floor x) (Succ c) Floor) (tri a x b c + tri a x b (Succ c) + tri a x b (Succ (Succ c)))
          := rewrite colsAt a x b c, colsAt a x b (Succ c), colsAt a x b (Succ (Succ c))
        _ = keep (cells r c) (window cells r c)
          := rewrite triCol cells r a x b ha hx hb c, triCol cells r a x b ha hx hb (Succ c), triCol cells r a x b ha hx hb (Succ (Succ c)), hx (Succ c)
    | False =>
      -- Past the last column both sides are floor.
      rewrite Vec.getOrPast (peelRow a x b) c Floor omega, <- hx (Succ c), Vec.getOrPast x c Floor omega

-- Row r (counted from 1) of a grid's rows, with a row of floor above the
-- first and past the last.
def rowB (rows: Vec (Vec Cell w) h) (r: Nat): Vec Cell w := Vec.getOr (VCons (Vec.replicate w Floor) rows) r (Vec.replicate w Floor)

theorem rowBIs (rows: Vec (Vec Cell w) h): (r: Nat) → RowIs (rowsCells rows) r (rowB rows r)
  | Zero, Zero => rfl
  | Zero, Succ j => Vec.getOrReplicate Floor w j
  | Succ r, Zero => rfl
  | Succ r, Succ j => rfl

-- Past the last row or column, everything is floor.
theorem rowsCellsBelow (rows: Vec (Vec Cell w) h) (r: Nat) (c: Nat) (hr: h ≤ r): rowsCells rows r c = Floor :=
  rewrite Vec.getOrPast rows r (Vec.replicate w Floor) hr in Vec.getOrReplicate Floor w c

theorem rowsCellsRight (rows: Vec (Vec Cell w) h) (r: Nat) (c: Nat) (hc: w ≤ c): rowsCells rows r c = Floor :=
  Vec.getOrPast (Vec.getOr rows r (Vec.replicate w Floor)) c Floor hc

-- One cell after a round: what `keep` leaves of it.
theorem cellRound (rows: Vec (Vec Cell w) h) (r: Nat) (c: Nat):
    rowsCells (roundRows rows) r c = keep (rowsCells rows r c) (window (rowsCells rows) r c) :=
  let gap := Vec.replicate w Floor
  match e: Nat.leq (Succ r) h with
    | True =>
      calc rowsCells (roundRows rows) r c
        _ = Vec.getOr (peelRow (rowB rows r) (rowB rows (Succ r)) (rowB rows (Succ (Succ r)))) c Floor
          := rewrite Vec.getOrAround rows r gap gap e peelRow
        _ = keep (rowsCells rows r c) (window (rowsCells rows) r c)
          := peelRowCells (rowsCells rows) r c (rowB rows r) (rowB rows (Succ r)) (rowB rows (Succ (Succ r)))
            (rowBIs rows r) (rowBIs rows (Succ r)) (rowBIs rows (Succ (Succ r)))
    | False =>
      rewrite rowsCellsBelow (roundRows rows) r c omega, rowsCellsBelow rows r c omega

-- The window, reindexed: positions at most 1 away.

-- Row (or column) x is at most 1 from r.
def near (r: Nat) (x: Nat): Bool := Nat.absDiff r x ≤ 1

-- At most 1 away is one below, the same, or one above.
theorem nearSplit (v: Nat): (r: Nat) → (x: Nat) →
    Nat.keepIf v (near r x) = Nat.keepIf v (Nat.equal r (Succ x)) + Nat.keepIf v (Nat.equal r x) + Nat.keepIf v (Nat.equal (Succ r) x)
  | Zero, Zero => omega
  | Zero, Succ Zero => rfl
  | Zero, Succ (Succ k) => rfl
  | Succ Zero, Zero => omega
  | Succ (Succ k), Zero => rfl
  | Succ r, Succ x => nearSplit v r x

-- `g` moved one place up: 0 at 0.
def shift (g: Nat → Nat): Nat → Nat
  | Zero => 0
  | Succ x => g x

theorem pickBelow (g: Nat → Nat) (n: Nat) (hz: (x: Nat) → n ≤ x → g x = 0): (r: Nat) →
    List.sumBy (List.range n) (x => Nat.keepIf (g x) (Nat.equal r (Succ x))) = shift g r
  | Zero => List.sumRangeNone (x => Nat.equal 0 (Succ x)) g n 0 (b h1 h2 => rfl)
  | Succ r => List.sumRangePick g n r (hz r)

-- A sum over 0, 1, …, n - 1 of the terms at most 1 from r: the three around
-- it, counted from 1. `g` is 0 past the end.
theorem nearSum (g: Nat → Nat) (n: Nat) (hz: (x: Nat) → n ≤ x → g x = 0) (r: Nat):
    List.sumBy (List.range n) (x => Nat.keepIf (g x) (near r x)) = shift g r + shift g (Succ r) + shift g (Succ (Succ r)) :=
  let below := (x: Nat) => Nat.keepIf (g x) (Nat.equal r (Succ x))
  let same := (x: Nat) => Nat.keepIf (g x) (Nat.equal r x)
  let above := (x: Nat) => Nat.keepIf (g x) (Nat.equal (Succ r) x)
  calc List.sumBy (List.range n) (x => Nat.keepIf (g x) (near r x))
    _ = List.sumBy (List.range n) (x => below x + same x + above x)
      := rewrite nearSplit _ r _
    _ = List.sumBy (List.range n) below + List.sumBy (List.range n) same + List.sumBy (List.range n) above
      := rewrite List.sumByAdd (List.range n) (x => below x + same x) above, List.sumByAdd (List.range n) below same
    _ = shift g r + g r + g (Succ r)
      := rewrite pickBelow g n hz r, List.sumRangePick g n r (hz r), List.sumRangePick g n (Succ r) (hz (Succ r))

-- Bool facts for splitting the sums.
theorem toNatAnd: (a: Bool) → (b: Bool) → Bool.toNat (a ∧ b) = Nat.keepIf (Bool.toNat b) a
  | True, b => rfl
  | False, b => rfl

theorem isRollCount: (a: Cell) → Bool.toNat (a == Roll) = a.count
  | Roll => rfl
  | Floor => rfl

-- Splitting off the position itself.
theorem splitSelf: (n1: Bool) → (n2: Bool) → (e: Bool) → (x: Bool) → (e = True → (n1 = True ∧ n2 = True)) →
    Bool.toNat (n1 ∧ n2 ∧ x) = Bool.toNat ((n1 ∧ n2 ∧ not e) ∧ x) + Bool.toNat (e ∧ x)
  | True, True, True, x, h => rfl
  | True, False, True, x, h => Void.exfalso (Bool.falseNotTrue (And.right (h rfl)))
  | False, n2, True, x, h => Void.exfalso (Bool.falseNotTrue (And.left (h rfl)))
  | True, True, False, x, h => omega
  | True, False, False, x, h => rfl
  | False, n2, False, x, h => rfl

theorem andKeep: (a: Bool) → (b: Bool) → (x: Bool) → Bool.toNat ((a ∧ b) ∧ x) = Nat.keepIf (Nat.keepIf (Bool.toNat x) b) a
  | True, True, x => rfl
  | True, False, x => rfl
  | False, b, x => rfl

theorem nearSelf (r: Nat): (Nat.absDiff r r ≤ 1) = True := rewrite Nat.absDiffSelf r

-- The position itself is at most 1 from itself.
theorem selfNear (r: Nat) (c: Nat) (x: Nat) (y: Nat) (h: (r == x ∧ c == y) = True): near r x = True ∧ near c y = True :=
  Both (rewrite DecEq.sound r x (Bool.andLeft (r == x) (c == y) h) in nearSelf x)
    (rewrite DecEq.sound c y (Bool.andRight (r == x) (c == y) h) in nearSelf y)

-- A count over the grid's positions is a sum of 1s and 0s.
theorem countPositionsSum (grid: Grid) (p: Nat → Nat → Bool):
    countPositions grid p = List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat (p x y))) :=
  rewrite List.countSumBy _ _

-- The sum over the grid's positions that picks out (r, c) itself.
theorem selfSum (grid: Grid) (cells: Cells) (below: (r: Nat) → (c: Nat) → grid.height ≤ r → cells r c = Floor)
    (right: (r: Nat) → (c: Nat) → grid.width ≤ c → cells r c = Floor) (r: Nat) (c: Nat):
    List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat ((r == x ∧ c == y) ∧ cells x y == Roll))) = (cells r c).count :=
  calc List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat ((r == x ∧ c == y) ∧ cells x y == Roll)))
    _ = List.sumBy (List.range grid.height) (x => Nat.keepIf (List.sumBy (List.range grid.width) (y => Nat.keepIf ((cells x y).count) (Nat.equal c y))) (Nat.equal r x))
      := rewrite Nat.eqIsEqual r _, Nat.eqIsEqual c _, andKeep _ _ _, isRollCount _, <- Nat.keepIfSumBy _ _ _
    _ = List.sumBy (List.range grid.height) (x => Nat.keepIf ((cells x c).count) (Nat.equal r x))
      := rewrite List.sumRangePick (y => (cells _ y).count) grid.width c (h => Eq.cong Cell.count (right _ c h))
    _ = (cells r c).count := List.sumRangePick (x => (cells x c).count) grid.height r (h => Eq.cong Cell.count (below r c h))

-- The rolls in row r (counted from 1), columns c, c + 1 and c + 2.
def rowSum (cells: Cells) (r: Nat) (c: Nat): Nat := (bord cells r c).count + (bord cells r (Succ c)).count + (bord cells r (Succ (Succ c))).count

theorem bordRowShift (cells: Cells) (x: Nat): (j: Nat) → shift (y => (cells x y).count) j = (bord cells (Succ x) j).count
  | Zero => rfl
  | Succ y => rfl

theorem rowSumShift (cells: Cells) (c: Nat): (r: Nat) → shift (x => rowSum cells (Succ x) c) r = rowSum cells r c
  | Zero => rfl
  | Succ x => rfl

theorem bordBelow (grid: Grid) (cells: Cells) (below: (r: Nat) → (c: Nat) → grid.height ≤ r → cells r c = Floor) (x: Nat) (hx: grid.height ≤ x):
    (j: Nat) → (bord cells (Succ x) j).count = 0
  | Zero => rfl
  | Succ y => Eq.cong Cell.count (below x y hx)

theorem rowSumBelow (grid: Grid) (cells: Cells) (below: (r: Nat) → (c: Nat) → grid.height ≤ r → cells r c = Floor) (c: Nat) (x: Nat) (hx: grid.height ≤ x):
    rowSum cells (Succ x) c = 0 :=
  rewrite bordBelow grid cells below x hx c, bordBelow grid cells below x hx (Succ c), bordBelow grid cells below x hx (Succ (Succ c))

-- The 3 by 3 block as a sum over all the grid's positions at most 1 away.
theorem nineSum (grid: Grid) (cells: Cells) (below: (r: Nat) → (c: Nat) → grid.height ≤ r → cells r c = Floor)
    (right: (r: Nat) → (c: Nat) → grid.width ≤ c → cells r c = Floor) (r: Nat) (c: Nat):
    List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat (near r x ∧ near c y ∧ cells x y == Roll)))
      = rowSum cells r c + rowSum cells (Succ r) c + rowSum cells (Succ (Succ r)) c :=
  calc List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat (near r x ∧ near c y ∧ cells x y == Roll)))
    _ = List.sumBy (List.range grid.height) (x => Nat.keepIf (List.sumBy (List.range grid.width) (y => Nat.keepIf ((cells x y).count) (near c y))) (near r x))
      := rewrite toNatAnd _ _, toNatAnd _ _, isRollCount _, <- Nat.keepIfSumBy _ _ _
    _ = List.sumBy (List.range grid.height) (x => Nat.keepIf (rowSum cells (Succ x) c) (near r x))
      := rewrite nearSum (y => (cells _ y).count) grid.width (y h => Eq.cong Cell.count (right _ y h)) c,
        bordRowShift cells _ c, bordRowShift cells _ (Succ c), bordRowShift cells _ (Succ (Succ c))
    _ = rowSum cells r c + rowSum cells (Succ r) c + rowSum cells (Succ (Succ r)) c
      := rewrite nearSum (x => rowSum cells (Succ x) c) grid.height (x h => rowSumBelow grid cells below c x h) r,
        rowSumShift cells c r, rowSumShift cells c (Succ r), rowSumShift cells c (Succ (Succ r))

-- The window by rows instead of columns.
theorem windowRows (cells: Cells) (r: Nat) (c: Nat): window cells r c = rowSum cells r c + rowSum cells (Succ r) c + rowSum cells (Succ (Succ r)) c :=
  omega

-- The window is the spec's neighbours and the cell itself, for cells that
-- are floor off the grid.
theorem windowIsNeighbours (grid: Grid) (cells: Cells) (below: (r: Nat) → (c: Nat) → grid.height ≤ r → cells r c = Floor)
    (right: (r: Nat) → (c: Nat) → grid.width ≤ c → cells r c = Floor) (r: Nat) (c: Nat):
    window cells r c = neighbours grid cells r c + (cells r c).count :=
  let adj := (x: Nat) => (y: Nat) => Bool.toNat (adjacent r c x y ∧ cells x y == Roll)
  let self := (x: Nat) => (y: Nat) => Bool.toNat ((r == x ∧ c == y) ∧ cells x y == Roll)
  calc window cells r c
    _ = rowSum cells r c + rowSum cells (Succ r) c + rowSum cells (Succ (Succ r)) c := windowRows cells r c
    _ = List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => Bool.toNat (near r x ∧ near c y ∧ cells x y == Roll)))
      := Eq.sym (nineSum grid cells below right r c)
    _ = List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => adj x y) + List.sumBy (List.range grid.width) (y => self x y))
      := rewrite splitSelf _ _ _ _ (selfNear r c _ _), List.sumByAdd [c := Nat] _ _ _
    _ = List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => adj x y))
        + List.sumBy (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => self x y))
      := List.sumByAdd (List.range grid.height) (x => List.sumBy (List.range grid.width) (y => adj x y)) (x => List.sumBy (List.range grid.width) (y => self x y))
    _ = neighbours grid cells r c + (cells r c).count
      := rewrite selfSum grid cells below right r c, countPositionsSum grid (x y => adjacent r c x y ∧ cells x y == Roll)
