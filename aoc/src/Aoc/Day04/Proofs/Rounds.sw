-- Facts about the puzzle's rounds, by positions: a round with an accessible
-- roll removes one (`roundCount`); once no roll is accessible the grid is
-- stable, and rounds change nothing (`roundsFixed`); so as many rounds as
-- there are rolls are enough (`roundsStable`), which is why Spec/Spec.sw
-- runs that many.

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Aoc.Day04.Spec (..)
import Std (And, Bool, Eq, List, Nat, Vec, Void)

theorem rollNotFloor (h: Floor = Roll): Void := Nat.zeroNotSucc 0 (Eq.cong Cell.count h)

theorem isRoll: (x: Cell) -> (x == Roll) = True -> x = Roll
  | Roll, h => rfl
  | Floor, h => Void.exfalso (Bool.falseNotTrue h)

-- The same cells everywhere.
def Same (s: Cells) (t: Cells): Prop := (r: Nat) -> (c: Nat) -> s r c = t r c

-- Floor everywhere off the grid.
def Inside (grid: Grid) (s: Cells): Prop :=
  ((r: Nat) -> (c: Nat) -> grid.height <= r -> s r c = Floor) && ((r: Nat) -> (c: Nat) -> grid.width <= c -> s r c = Floor)

theorem insideRows (grid: Grid) (rows: Vec (Vec Cell grid.width) grid.height): Inside grid (rowsCells rows) :=
  Both (r c h => rowsCellsBelow rows r c h) (r c h => rowsCellsRight rows r c h)

-- Every roll of `k` has at least 4 neighbours in `k`.
def Stable (grid: Grid) (k: Cells): Prop := (r: Nat) -> (c: Nat) -> k r c = Roll -> 4 <= neighbours grid k r c

-- Counts over positions agree for conditions that agree.
theorem countPositionsCongr (grid: Grid) (p: Nat -> Nat -> Bool) (q: Nat -> Nat -> Bool) (h: (r: Nat) -> (c: Nat) -> p r c = q r c):
    countPositions grid p = countPositions grid q :=
  rewrite countPositionsSum grid p, countPositionsSum grid q in
    List.sumByCong (x => List.sumBy (y => Bool.toNat (p x y)) (List.range grid.width)) (x => List.sumBy (y => Bool.toNat (q x y)) (List.range grid.width))
      (List.range grid.height)
      (x => List.sumByCong (y => Bool.toNat (p x y)) (y => Bool.toNat (q x y)) (List.range grid.width) (y => Eq.cong Bool.toNat (h x y)))

theorem rollCountSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t): rollCount grid s = rollCount grid t :=
  countPositionsCongr grid (r c => s r c == Roll) (r c => t r c == Roll) (r c => Eq.cong (x => x == Roll) (h r c))

-- Stability is about the cells only.
theorem neighboursSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t) (r: Nat) (c: Nat): neighbours grid s r c = neighbours grid t r c :=
  countPositionsCongr grid (x y => adjacent r c x y && s x y == Roll) (x y => adjacent r c x y && t x y == Roll)
    (x y => Eq.cong (v => adjacent r c x y && v == Roll) (h x y))

theorem stableSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t) (stable: Stable grid s): Stable grid t :=
  r c ht => rewrite <- neighboursSame grid s t h r c in stable r c (Eq.trans (h r c) ht)

-- The rounds.

theorem accessibleSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t) (r: Nat) (c: Nat): accessible grid s r c = accessible grid t r c :=
  calc accessible grid s r c
    _ = (t r c == Roll && neighbours grid s r c < 4) := rewrite h r c
    _ = accessible grid t r c := rewrite neighboursSame grid s t h r c

theorem removeSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t): Same (removeAccessible grid s) (removeAccessible grid t) :=
  r c => Eq.trans (Eq.cong (b => if b then Floor else s r c) (accessibleSame grid s t h r c)) (Eq.cong (v => if accessible grid t r c then Floor else v) (h r c))

theorem roundsSame (grid: Grid): (n: Nat) -> (s: Cells) -> (t: Cells) -> Same s t -> Same (rounds grid n s) (rounds grid n t)
  | Zero, s, t, h, r, c => h r c
  | Succ n, s, t, h, r, c => roundsSame grid n (removeAccessible grid s) (removeAccessible grid t) (removeSame grid s t h) r c

theorem ifFloorKeep: (b: Bool) -> (x: Cell) -> x = Floor -> (if b then Floor else x) = Floor
  | True, x, h => rfl
  | False, x, h => h

theorem removeInside (grid: Grid) (s: Cells) (ins: Inside grid s): Inside grid (removeAccessible grid s) :=
  Both (r c h => ifFloorKeep (accessible grid s r c) (s r c) (And.left ins r c h))
    (r c h => ifFloorKeep (accessible grid s r c) (s r c) (And.right ins r c h))

-- A round removes the accessible rolls, and no others.

def accCount (grid: Grid) (s: Cells): Nat := countPositions grid (r c => accessible grid s r c)

theorem roundTerm: (b: Bool) -> (x: Cell) -> (b = True -> x = Roll) ->
    Bool.toNat ((if b then Floor else x) == Roll) + Bool.toNat b = Bool.toNat (x == Roll)
  | True, x, hb => rewrite hb rfl
  | False, x, hb => omega

theorem roundCount (grid: Grid) (s: Cells): rollCount grid (removeAccessible grid s) + accCount grid s = rollCount grid s :=
  let gone := (r: Nat) => (c: Nat) => Bool.toNat (removeAccessible grid s r c == Roll)
  let acc := (r: Nat) => (c: Nat) => Bool.toNat (accessible grid s r c)
  calc rollCount grid (removeAccessible grid s) + accCount grid s
    _ = List.sumBy (x => List.sumBy (y => gone x y) (List.range grid.width)) (List.range grid.height)
        + List.sumBy (x => List.sumBy (y => acc x y) (List.range grid.width)) (List.range grid.height)
      := rewrite countPositionsSum grid (r c => removeAccessible grid s r c == Roll), countPositionsSum grid (r c => accessible grid s r c)
    _ = List.sumBy (x => List.sumBy (y => gone x y) (List.range grid.width) + List.sumBy (y => acc x y) (List.range grid.width)) (List.range grid.height)
      := Eq.sym (List.sumByAdd (x => List.sumBy (y => gone x y) (List.range grid.width)) (x => List.sumBy (y => acc x y) (List.range grid.width)) (List.range grid.height))
    _ = List.sumBy (x => List.sumBy (y => Bool.toNat (s x y == Roll)) (List.range grid.width)) (List.range grid.height)
      := List.sumByCong (x => List.sumBy (y => gone x y) (List.range grid.width) + List.sumBy (y => acc x y) (List.range grid.width))
        (x => List.sumBy (y => Bool.toNat (s x y == Roll)) (List.range grid.width))
        (List.range grid.height)
        (x => Eq.trans (Eq.sym (List.sumByAdd (y => gone x y) (y => acc x y) (List.range grid.width)))
          (List.sumByCong (y => gone x y + acc x y) (y => Bool.toNat (s x y == Roll))
            (List.range grid.width)
            (y => roundTerm (accessible grid s x y) (s x y) (h => isRoll (s x y) (Bool.andLeft (s x y == Roll) (neighbours grid s x y < 4) h)))))
    _ = rollCount grid s := Eq.sym (countPositionsSum grid (r c => s r c == Roll))

theorem toNatZero: (b: Bool) -> Bool.toNat b = 0 -> b = False
  | False, h => rfl
  | True, h => omega

-- A count over positions that is 0 holds nowhere on the grid.
theorem countNone (grid: Grid) (p: Nat -> Nat -> Bool) (h: countPositions grid p = 0) (r: Nat) (c: Nat) (hr: r < grid.height) (hc: c < grid.width): p r c = False :=
  let sums := Eq.trans (Eq.sym (countPositionsSum grid p)) h
  let row := List.sumRangeZero (x => List.sumBy (y => Bool.toNat (p x y)) (List.range grid.width)) grid.height 0 sums r omega hr
  toNatZero (p r c) (List.sumRangeZero (y => Bool.toNat (p r y)) grid.width 0 row c omega hc)

-- Off the grid or not a roll: nothing to check.
theorem stableWhere (grid: Grid) (s: Cells) (ins: Inside grid s) (good: (r: Nat) -> (c: Nat) -> r < grid.height -> c < grid.width -> s r c = Roll -> 4 <= neighbours grid s r c):
    Stable grid s :=
  r c hs =>
    match e1: Nat.leq (Succ r) grid.height, e2: Nat.leq (Succ c) grid.width with
      | True, True => good r c e1 e2 hs
      | False, b => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym (And.left ins r c omega)) hs))
      | True, False => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym (And.right ins r c omega)) hs))

-- A roll that isn't accessible has at least 4 neighbours.
theorem andTrueLeft: (a: Bool) -> (b: Bool) -> a = True -> (a && b) = False -> b = False
  | True, b, ha, h => h
  | False, b, ha, h => Void.exfalso (Bool.falseNotTrue ha)

theorem rollIsRoll (x: Cell) (h: x = Roll): (x == Roll) = True := rewrite h in rfl

theorem notAccessible (grid: Grid) (s: Cells) (r: Nat) (c: Nat) (h: accessible grid s r c = False) (hs: s r c = Roll): 4 <= neighbours grid s r c :=
  let few: Nat.leq (Succ (neighbours grid s r c)) 4 = False :=
    andTrueLeft (s r c == Roll) (neighbours grid s r c < 4) (rollIsRoll (s r c) hs) h
  omega

-- No accessible roll: stable.
theorem noneStable (grid: Grid) (s: Cells) (ins: Inside grid s) (h: accCount grid s = 0): Stable grid s :=
  stableWhere grid s ins (r c hr hc hs => notAccessible grid s r c (countNone grid (r c => accessible grid s r c) h r c hr hc) hs)

theorem stableNotAccessible (grid: Grid) (s: Cells) (stable: Stable grid s) (r: Nat) (c: Nat): accessible grid s r c = False :=
  match e: s r c with
    | Floor => rfl
    | Roll => omega [stable r c e]

-- Once stable, rounds change nothing.
theorem roundsFixed (grid: Grid): (n: Nat) -> (s: Cells) -> Stable grid s -> Same (rounds grid n s) s
  | Zero, s, stable, r, c => rfl
  | Succ n, s, stable, r, c =>
    let same: Same (removeAccessible grid s) s := x y => rewrite stableNotAccessible grid s stable x y in rfl
    Eq.trans (roundsSame grid n (removeAccessible grid s) s same r c) (roundsFixed grid n s stable r c)

-- As many rounds as there are rolls leave no accessible roll.
theorem roundsStable (grid: Grid): (fuel: Nat) -> (s: Cells) -> Inside grid s -> rollCount grid s <= fuel -> Stable grid (rounds grid fuel s)
  | Zero, s, ins, h, r, c, hs =>
    stableWhere grid s ins (x y hx hy hxy =>
      Void.exfalso (Bool.trueNotFalse
        (Eq.trans (Eq.sym (rollIsRoll (s x y) hxy))
          (countNone grid (x y => s x y == Roll) omega x y hx hy)))) r c hs
  | Succ n, s, ins, h, r, c, hs =>
    match e: accCount grid s with
      | Zero =>
        let stable := noneStable grid s ins e
        stableSame grid s (rounds grid (Succ n) s) (x y => Eq.sym (roundsFixed grid (Succ n) s stable x y)) stable r c hs
      | Succ b =>
        let total: rollCount grid (removeAccessible grid s) + Succ b <= Succ n := rewrite <- e, roundCount grid s in h
        roundsStable grid n (removeAccessible grid s) (removeInside grid s ins)
          omega r c hs
