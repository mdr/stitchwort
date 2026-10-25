-- Why looking at the key columns and rows is enough (`allKeysIsSpec`): a
-- rectangle with two red tiles as corners is all red and green exactly when
-- its key tiles are.
--   1. Whether a tile is red or green depends only on how its column
--      compares with the red tiles' columns, and its row with their rows
--      (`redOrGreenSame`): every test in the spec compares the tile with the
--      ends of a straight line, which are red tiles.
--   2. Every column from one red tile's column to another's compares with
--      the red tiles' columns as a key column in that range does
--      (`representative`): the column itself if it is a red tile's, else the
--      column just right of the nearest red tile's column to its left.
--   3. The key columns are sorted, so those from one corner's position to
--      the other's are the key columns from one corner's column to the
--      other's (`List.sortedGetOrLe`, `List.sortedBetween`).

namespace Aoc.Day09.Proofs
import Aoc.Day09 (..)
import Aoc.Day09.Spec (..)
import Std (Bool, Eq, List, Nat, Void)

-- `v` and `w` compare the same way with each of `values`.
def SameSide (values: List Nat) (v: Nat) (w: Nat): Prop :=
  (c: Nat) -> List.Mem c values -> And (Nat.leq c v = Nat.leq c w) (Nat.leq v c = Nat.leq w c)

def columnsOf (tiles: List Tile): List Nat := tiles.map (tile => tile.x)

def rowsOf (tiles: List Tile): List Nat := tiles.map (tile => tile.y)

-- 1. Only comparisons with the red tiles matter ------------------------------

theorem lessSame (values: List Nat) (u: Nat) (v: Nat) (w: Nat) (m: List.Mem u values) (s: SameSide values v w):
    Nat.leq (Succ v) u = Nat.leq (Succ w) u :=
  rewrite Nat.lessNotLe v u, Nat.lessNotLe w u, (s u m).left in rfl

theorem fromSame (values: List Nat) (one: Nat) (other: Nat) (v: Nat) (w: Nat) (m1: List.Mem one values) (m2: List.Mem other values) (s: SameSide values v w):
    from one other v = from one other w :=
  rewrite (s one m1).left, (s one m1).right, (s other m2).left, (s other m2).right in rfl

-- The ends of a straight line of the loop are red tiles.
theorem connectionEnds (tiles: List Tile) (ends: (Tile, Tile)) (m: List.Mem ends (connections tiles)):
    And (List.Mem ends.fst tiles) (List.Mem ends.snd tiles) :=
  match List.memZip ends tiles (List.append (List.drop tiles 1) (List.take tiles 1)) m with
    | Both first second =>
      Both first
        (match List.memAppend ends.snd (List.drop tiles 1) (List.take tiles 1) second with
          | Inl d => List.memDrop tiles ends.snd 1 d
          | Inr t => List.memTake tiles ends.snd 1 t)

theorem columnIn (tiles: List Tile) (tile: Tile) (m: List.Mem tile tiles): List.Mem tile.x (columnsOf tiles) := List.memMap tiles tile m (tile => tile.x)

theorem rowIn (tiles: List Tile) (tile: Tile) (m: List.Mem tile tiles): List.Mem tile.y (rowsOf tiles) := List.memMap tiles tile m (tile => tile.y)

theorem onStraightLineSame (tiles: List Tile) (x: Nat) (y: Nat) (x2: Nat) (y2: Nat) (sx: SameSide (columnsOf tiles) x x2) (sy: SameSide (rowsOf tiles) y y2)
    (ends: (Tile, Tile)) (m: List.Mem ends (connections tiles)):
    onStraightLine { x, y } ends = onStraightLine { x = x2, y = y2 } ends :=
  match connectionEnds tiles ends m with
    | Both first second =>
      rewrite fromSame (columnsOf tiles) ends.fst.x ends.snd.x x x2 (columnIn tiles ends.fst first) (columnIn tiles ends.snd second) sx,
        fromSame (rowsOf tiles) ends.fst.y ends.snd.y y y2 (rowIn tiles ends.fst first) (rowIn tiles ends.snd second) sy
        in rfl

theorem crossesRaySame (tiles: List Tile) (x: Nat) (y: Nat) (x2: Nat) (y2: Nat) (sx: SameSide (columnsOf tiles) x x2) (sy: SameSide (rowsOf tiles) y y2)
    (ends: (Tile, Tile)) (m: List.Mem ends (connections tiles)):
    crossesRay { x, y } ends = crossesRay { x = x2, y = y2 } ends :=
  match connectionEnds tiles ends m with
    | Both first second =>
      let fy := rowIn tiles ends.fst first
      let sy2 := rowIn tiles ends.snd second
      rewrite lessSame (columnsOf tiles) ends.fst.x x x2 (columnIn tiles ends.fst first) sx,
        lessSame (rowsOf tiles) ends.snd.y y y2 sy2 sy,
        lessSame (rowsOf tiles) ends.fst.y y y2 fy sy,
        (sy ends.fst.y fy).left,
        (sy ends.snd.y sy2).left
        in rfl

-- Tiles whose columns and rows compare alike with the red tiles' are alike.
theorem redOrGreenSame (tiles: List Tile) (x: Nat) (y: Nat) (x2: Nat) (y2: Nat) (sx: SameSide (columnsOf tiles) x x2) (sy: SameSide (rowsOf tiles) y y2):
    redOrGreen tiles { x, y } = redOrGreen tiles { x = x2, y = y2 } :=
  rewrite onStraightLineSame tiles x y x2 y2 sx sy, crossesRaySame tiles x y x2 y2 sx sy in rfl

-- 2. A key value for every value -------------------------------------------

-- A value at or after the smallest of `values` compares with them as some
-- key value does: a value or one just after one, from `low` up to it.
theorem representative (values: List Nat) (v: Nat) (low: Nat) (lowIn: List.Mem low values) (lowLe: low <= v) (goal: Prop)
    (use: (w: Nat) -> Or (List.Mem w values) (List.Mem w (List.map values Succ)) -> low <= w -> w <= v -> SameSide values v w -> goal): goal :=
  let atMost := List.filter values (c => c <= v)
  let nearest := largest atMost
  let lowAtMost: List.Mem low atMost := List.memFilterIntro values (c => c <= v) low lowIn lowLe
  -- Every value up to v is at most the nearest.
  let below: (c: Nat) -> List.Mem c values -> c <= v -> c <= nearest :=
    c m h => (largestIsLargest atMost).left c (List.memFilterIntro values (c => c <= v) c m h)
  let nearestIn: And (List.Mem nearest values) (Nat.leq nearest v = True) :=
    match largestInList atMost with
      | Inl m => List.memFilter values (c => c <= v) nearest m
      | Inr (Both empty zero) => Void.exfalso (rewrite empty at lowAtMost)
  match nearestIn with
    | Both nearestMem nearestLe =>
      let lowLeNearest := below low lowIn lowLe
      match e: Nat.leq v nearest with
        -- v is one of the values.
        | True => use v (Inl (rewrite (omega: nearest = v) at nearestMem)) lowLe (Nat.leRefl v) (c m => Both rfl rfl)
        -- v isn't: the value just after the nearest compares alike.
        | False =>
          use (Succ nearest) (Inr (List.memMap values nearest nearestMem Succ)) (omega) (omega)
            (c m => Both
              (match cv: Nat.leq c v with
                | True => Eq.sym (omega [below c m cv])
                | False => Eq.sym (omega))
              (match vc: Nat.leq v c with
                | True => Eq.sym (omega)
                | False => Eq.sym (omega [below c m (omega)])))

-- 3. The key columns and rows are sorted -------------------------------------

theorem keyLinesSorted (values: List Nat): List.Sorted Nat.leq (keyLines values) :=
  List.sortedDedup Nat.leq (List.sort (List.append values (List.map values Succ))) (List.sortSortedNat (List.append values (List.map values Succ)))

-- Each value, and each one just after a value, is a key value.
theorem keyLinesHas (values: List Nat) (v: Nat) (m: Or (List.Mem v values) (List.Mem v (List.map values Succ))): List.Mem v (keyLines values) :=
  let all := List.append values (List.map values Succ)
  let inAll: List.Mem v all :=
    match m with
      | Inl l => List.anyAppendLeft (w => w = v) values (List.map values Succ) l
      | Inr r => List.anyAppendRight (w => w = v) values (List.map values Succ) r
  List.memDedupIntro v (List.sort all) (List.memPerm all (List.sort all) (List.permSym (List.sort all) all (List.sortPerm all)) v inAll)

-- On a sorted list holding u and v, the elements at their positions, the
-- lower position first, are the smaller and the larger of them.
theorem axisEnds (xs: List Nat) (s: List.Sorted Nat.leq xs) (u: Nat) (v: Nat) (mu: List.Mem u xs) (mv: List.Mem v xs):
    And (And (List.getOr xs 0 (Nat.min (List.indexOf xs u) (List.indexOf xs v)) = Nat.min u v)
        (List.getOr xs 0 (Nat.max (List.indexOf xs u) (List.indexOf xs v)) = Nat.max u v))
      (Nat.max (List.indexOf xs u) (List.indexOf xs v) < List.length xs) :=
  let i := List.indexOf xs u
  let j := List.indexOf xs v
  let atI: List.getOr xs 0 i = u := List.getOrIndexOf xs 0 u mu
  let atJ: List.getOr xs 0 j = v := List.getOrIndexOf xs 0 v mv
  let iIn: i < List.length xs := List.indexOfLt xs u mu
  let jIn: j < List.length xs := List.indexOfLt xs v mv
  match e: Nat.leq i j with
    | True =>
      let le := List.sortedGetOrLe xs 0 s i j e jIn
      Both (Both (omega) (omega)) jIn
    | False =>
      let le := List.sortedGetOrLe xs 0 s j i (omega) iIn
      Both (Both (omega) (omega)) iIn

-- The elements from one position to the other lie from the smaller value to the larger.
theorem axisInside (xs: List Nat) (s: List.Sorted Nat.leq xs) (u: Nat) (v: Nat) (mu: List.Mem u xs) (mv: List.Mem v xs)
    (k: Nat) (lo: Nat.min (List.indexOf xs u) (List.indexOf xs v) <= k) (hi: k <= Nat.max (List.indexOf xs u) (List.indexOf xs v)):
    And (Nat.min u v <= List.getOr xs 0 k) (List.getOr xs 0 k <= Nat.max u v) :=
  match axisEnds xs s u v mu mv with
    | Both (Both atMin atMax) maxIn =>
      let up := List.sortedGetOrLe xs 0 s (Nat.min (List.indexOf xs u) (List.indexOf xs v)) k lo (omega)
      let down := List.sortedGetOrLe xs 0 s k (Nat.max (List.indexOf xs u) (List.indexOf xs v)) hi maxIn
      Both (omega) (omega)

-- And every element of the list from the smaller value to the larger is at
-- such a position: what holds at each holds for it.
theorem axisCovers (xs: List Nat) (s: List.Sorted Nat.leq xs) (u: Nat) (v: Nat) (mu: List.Mem u xs) (mv: List.Mem v xs) (p: Nat -> Prop)
    (each: (k: Nat) -> Nat.min (List.indexOf xs u) (List.indexOf xs v) <= k -> k <= Nat.max (List.indexOf xs u) (List.indexOf xs v) -> p (List.getOr xs 0 k))
    (w: Nat) (mw: List.Mem w xs) (lo: Nat.min u v <= w) (hi: w <= Nat.max u v): p w :=
  match axisEnds xs s u v mu mv with
    | Both (Both atMin atMax) maxIn =>
      List.sortedBetween 0 p xs s (Nat.min (List.indexOf xs u) (List.indexOf xs v)) (Nat.max (List.indexOf xs u) (List.indexOf xs v)) (omega) maxIn
        each w mw (omega) (omega)

-- The smaller of two values is one of them.
theorem minIn (values: List Nat) (u: Nat) (v: Nat) (mu: List.Mem u values) (mv: List.Mem v values): List.Mem (Nat.min u v) values :=
  match e: Nat.leq u v with
    | True => mu
    | False => mv

-- The rectangle between two red tiles is all red and green exactly when its
-- key tiles are.
theorem allKeysIsSpec (tiles: List Tile) (a: Tile) (b: Tile) (ma: List.Mem a tiles) (mb: List.Mem b tiles):
    allKeys tiles ((Floor.of tiles).corner a) ((Floor.of tiles).corner b) = allRedOrGreen tiles (a, b) :=
  let floor := Floor.of tiles
  let columns := floor.columns
  let rows := floor.rows
  let sc: List.Sorted Nat.leq columns := keyLinesSorted (columnsOf tiles)
  let sr: List.Sorted Nat.leq rows := keyLinesSorted (rowsOf tiles)
  let ax := columnIn tiles a ma
  let bx := columnIn tiles b mb
  let ay := rowIn tiles a ma
  let by := rowIn tiles b mb
  let keyAx: List.Mem a.x columns := keyLinesHas (columnsOf tiles) a.x (Inl ax)
  let keyBx: List.Mem b.x columns := keyLinesHas (columnsOf tiles) b.x (Inl bx)
  let keyAy: List.Mem a.y rows := keyLinesHas (rowsOf tiles) a.y (Inl ay)
  let keyBy: List.Mem b.y rows := keyLinesHas (rowsOf tiles) b.y (Inl by)
  Bool.eqOf (allKeys tiles (floor.corner a) (floor.corner b)) (allRedOrGreen tiles (a, b))
    -- Every tile is red or green like a key tile in the rectangle.
    (keys =>
      List.allBetweenIntro _ (Nat.min a.y b.y) (Nat.max a.y b.y) (y ylo yhi =>
        List.allBetweenIntro _ (Nat.min a.x b.x) (Nat.max a.x b.x) (x xlo xhi =>
          representative (columnsOf tiles) x (Nat.min a.x b.x) (minIn (columnsOf tiles) a.x b.x ax bx) xlo (redOrGreen tiles { x, y } = True)
            (keyX keyXIn keyXLo keyXHi sx =>
              representative (rowsOf tiles) y (Nat.min a.y b.y) (minIn (rowsOf tiles) a.y b.y ay by) ylo (redOrGreen tiles { x, y } = True)
                (keyY keyYIn keyYLo keyYHi sy =>
                  rewrite redOrGreenSame tiles x y keyX keyY sx sy in
                    axisCovers rows sr a.y b.y keyAy keyBy (w => redOrGreen tiles { x = keyX, y = w } = True)
                      (r rlo rhi =>
                        axisCovers columns sc a.x b.x keyAx keyBx (v => redOrGreen tiles { x = v, y = List.getOr rows 0 r } = True)
                          (c clo chi => List.allBetweenElim _ _ _ (List.allBetweenElim _ _ _ keys r rlo rhi) c clo chi)
                          keyX (keyLinesHas (columnsOf tiles) keyX keyXIn) keyXLo (omega))
                      keyY (keyLinesHas (rowsOf tiles) keyY keyYIn) keyYLo (omega))))))
    -- Every key tile in the rectangle is a tile of it.
    (spec =>
      List.allBetweenIntro _ _ _ (r rlo rhi =>
        List.allBetweenIntro _ _ _ (c clo chi =>
          let yIn := axisInside rows sr a.y b.y keyAy keyBy r rlo rhi
          let xIn := axisInside columns sc a.x b.x keyAx keyBx c clo chi
          List.allBetweenElim _ _ _ (List.allBetweenElim _ _ _ spec (List.getOr rows 0 r) yIn.left yIn.right) (List.getOr columns 0 c) xIn.left xIn.right)))
