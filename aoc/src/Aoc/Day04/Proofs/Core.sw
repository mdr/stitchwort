-- Part 2's main argument, about any way of removing rolls. Call a set of
-- rolls stable when every roll in it has at least 4 neighbours in it. A
-- step that removes only rolls accessible at the time never removes a roll
-- of a stable set inside the grid (`stepKeeps`): such a roll always has its
-- 4 neighbours. So a process of such steps that ends with no accessible roll
-- ends at a stable set that contains every stable set inside the grid: the
-- largest one, the "core". Two such processes end at the same rolls
-- (`endsAgree`). The puzzle's rounds are one such process (`roundsKeep`,
-- `roundsStable`: as many rounds as there are rolls are enough); the
-- program's sweep is another (Proofs/Sweep.sw).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (And, Bool, Decidable, Eq, List, Nat, Void)

theorem rollNotFloor (h: Floor = Roll): Void := Nat.zeroNotSucc 0 (Eq.cong Cell.count h)

theorem isRoll: (x: Cell) -> (x == Roll) = True -> x = Roll
  | Roll,  h => rfl
  | Floor, h => Void.exfalso (Bool.falseNotTrue h)

-- Every roll of `k` is a roll of `s`.
def Sub (k: Cells) (s: Cells): Prop := (r: Nat) -> (c: Nat) -> k r c = Roll -> s r c = Roll

theorem subRefl (s: Cells): Sub s s := r c h => h

theorem subTrans (a: Cells) (b: Cells) (d: Cells) (h1: Sub a b) (h2: Sub b d): Sub a d := r c h => h2 r c (h1 r c h)

-- The same cells everywhere.
def Same (s: Cells) (t: Cells): Prop := (r: Nat) -> (c: Nat) -> s r c = t r c

-- Floor everywhere off the grid.
def Inside (grid: Grid) (s: Cells): Prop :=
  ((r: Nat) -> (c: Nat) -> grid.height <= r -> s r c = Floor) && ((r: Nat) -> (c: Nat) -> grid.width <= c -> s r c = Floor)

theorem insideGrid (grid: Grid): Inside grid (cellsOf grid) :=
  Both (r c h => rowsCellsBelow grid.rows r c h) (r c h => rowsCellsRight grid.rows r c h)

-- Every roll of `k` has at least 4 neighbours in `k`.
def Stable (grid: Grid) (k: Cells): Prop := (r: Nat) -> (c: Nat) -> k r c = Roll -> 4 <= neighbours grid k r c

-- `t` is `s` with some rolls removed, each of them accessible in `s`.
def Step (grid: Grid) (s: Cells) (t: Cells): Prop :=
  Sub t s && ((r: Nat) -> (c: Nat) -> s r c = Roll -> t r c = Floor -> neighbours grid s r c < 4)

-- `s` still holds every stable set of rolls inside `s0`.
def Keeps (grid: Grid) (s0: Cells) (s: Cells): Prop := (k: Cells) -> Stable grid k -> Sub k s0 -> Sub k s

-- Counts over positions agree for conditions that agree.
theorem countPositionsCongr (grid: Grid) (p: Nat -> Nat -> Bool) (q: Nat -> Nat -> Bool) (h: (r: Nat) -> (c: Nat) -> p r c = q r c):
    countPositions grid p = countPositions grid q :=
  rewrite countPositionsSum grid p, countPositionsSum grid q in
    List.sumByCong (x => List.sumBy (y => Bool.toNat (p x y)) (List.range grid.width)) (x => List.sumBy (y => Bool.toNat (q x y)) (List.range grid.width))
      (List.range grid.height)
      (x => List.sumByCong (y => Bool.toNat (p x y)) (y => Bool.toNat (q x y)) (List.range grid.width) (y => Eq.cong Bool.toNat (h x y)))

-- More rolls, at least as many neighbours.
theorem termLe: (b: Bool) -> (p: Cell) -> (q: Cell) -> (p = Roll -> q = Roll) -> Bool.toNat (b && p == Roll) <= Bool.toNat (b && q == Roll)
  | False, p,     q,     h => rfl
  | True,  Floor, q,     h => rfl
  | True,  Roll,  Roll,  h => rfl
  | True,  Roll,  Floor, h => Void.exfalso (rollNotFloor (h rfl))

theorem neighboursMono (grid: Grid) (k: Cells) (s: Cells) (h: Sub k s) (r: Nat) (c: Nat): neighbours grid k r c <= neighbours grid s r c :=
  rewrite countPositionsSum grid (x y => adjacent r c x y && k x y == Roll), countPositionsSum grid (x y => adjacent r c x y && s x y == Roll) in
    List.sumByLe (x => List.sumBy (y => Bool.toNat (adjacent r c x y && s x y == Roll)) (List.range grid.width))
      (x => List.sumBy (y => Bool.toNat (adjacent r c x y && k x y == Roll)) (List.range grid.width))
      (x => List.sumByLe (y => Bool.toNat (adjacent r c x y && s x y == Roll)) (y => Bool.toNat (adjacent r c x y && k x y == Roll))
         (y => termLe (adjacent r c x y) (k x y) (s x y) (h x y)) (List.range grid.width))
      (List.range grid.height)

-- A step never removes a roll of a stable set.
theorem stepKeeps (grid: Grid) (s: Cells) (t: Cells) (step: Step grid s t) (k: Cells) (stable: Stable grid k) (ks: Sub k s): Sub k t :=
  r c hk =>
    match e: t r c with
      | Roll  => rfl
      | Floor =>
        let few: neighbours grid s r c < 4 := And.right step r c (ks r c hk) e
        let many: 4 <= neighbours grid s r c :=
          Nat.leTrans 4 (neighbours grid k r c) (neighbours grid s r c) (stable r c hk) (neighboursMono grid k s ks r c)
        Void.exfalso (Nat.lessIrrefl (neighbours grid s r c) (Nat.leTrans (Succ (neighbours grid s r c)) 4 (neighbours grid s r c) few many))

theorem keepsStep (grid: Grid) (s0: Cells) (s: Cells) (t: Cells) (hk: Keeps grid s0 s) (step: Step grid s t): Keeps grid s0 t :=
  k stable ks0 => stepKeeps grid s t step k stable (hk k stable ks0)

-- Two sets that each hold the other are the same.
theorem subSame (a: Cells) (b: Cells) (h1: Sub a b) (h2: Sub b a) (r: Nat) (c: Nat): a r c = b r c :=
  match e1: a r c, e2: b r c with
    | Roll,  Roll  => rfl
    | Floor, Floor => rfl
    | Roll,  Floor => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym e2) (h1 r c e1)))
    | Floor, Roll  => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym e1) (h2 r c e2)))

-- The ends of two processes: each stable, inside `s0`, and holding every
-- stable set inside `s0`. They are the same.
theorem endsAgree (grid: Grid) (s0: Cells) (f1: Cells) (f2: Cells)
    (sub1: Sub f1 s0) (stable1: Stable grid f1) (keeps1: Keeps grid s0 f1)
    (sub2: Sub f2 s0) (stable2: Stable grid f2) (keeps2: Keeps grid s0 f2): Same f1 f2 :=
  subSame f1 f2 (keeps2 f1 stable1 sub1) (keeps1 f2 stable2 sub2)

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
    _ = (t r c == Roll && neighbours grid s r c < 4) := Eq.cong (v => v == Roll && neighbours grid s r c < 4) (h r c)
    _ = accessible grid t r c := Eq.cong (n => t r c == Roll && n < 4) (neighboursSame grid s t h r c)

theorem removeSame (grid: Grid) (s: Cells) (t: Cells) (h: Same s t): Same (removeAccessible grid s) (removeAccessible grid t) :=
  r c => Eq.trans (Eq.cong (b => if b then Floor else s r c) (accessibleSame grid s t h r c)) (Eq.cong (v => if accessible grid t r c then Floor else v) (h r c))

theorem roundsSame (grid: Grid): (n: Nat) -> (s: Cells) -> (t: Cells) -> Same s t -> Same (rounds grid n s) (rounds grid n t)
  | Zero,   s, t, h, r, c => h r c
  | Succ n, s, t, h, r, c => roundsSame grid n (removeAccessible grid s) (removeAccessible grid t) (removeSame grid s t h) r c

theorem ifFloorRoll: (b: Bool) -> (x: Cell) -> (if b then Floor else x) = Roll -> (b = False && x = Roll)
  | True,  x, h => Void.exfalso (rollNotFloor h)
  | False, x, h => Both rfl h

theorem ifFloorFloor: (b: Bool) -> (x: Cell) -> x = Roll -> (if b then Floor else x) = Floor -> b = True
  | True,  x, hx, h => rfl
  | False, x, hx, h => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym h) hx))

-- An accessible roll has fewer than 4 neighbours.
theorem accessibleFew (grid: Grid) (s: Cells) (r: Nat) (c: Nat) (h: accessible grid s r c = True): neighbours grid s r c < 4 :=
  Decidable.toBoolSound (Nat.decLessThan (neighbours grid s r c) 4) (Bool.andRight (s r c == Roll) (neighbours grid s r c < 4) h)

-- A round is a step.
theorem removeStep (grid: Grid) (s: Cells): Step grid s (removeAccessible grid s) :=
  Both (r c h => And.right (ifFloorRoll (accessible grid s r c) (s r c) h))
    (r c hs ht => accessibleFew grid s r c (ifFloorFloor (accessible grid s r c) (s r c) hs ht))

theorem ifFloorKeep: (b: Bool) -> (x: Cell) -> x = Floor -> (if b then Floor else x) = Floor
  | True,  x, h => rfl
  | False, x, h => h

theorem removeInside (grid: Grid) (s: Cells) (ins: Inside grid s): Inside grid (removeAccessible grid s) :=
  Both (r c h => ifFloorKeep (accessible grid s r c) (s r c) (And.left ins r c h))
    (r c h => ifFloorKeep (accessible grid s r c) (s r c) (And.right ins r c h))

-- Rounds keep the stable sets, and stay inside the grid's rolls.
theorem roundsKeep (grid: Grid) (s0: Cells): (n: Nat) -> (s: Cells) -> Keeps grid s0 s -> Sub s s0 ->
    (Keeps grid s0 (rounds grid n s) && Sub (rounds grid n s) s0)
  | Zero,   s, hk, hs => Both hk hs
  | Succ n, s, hk, hs =>
    roundsKeep grid s0 n (removeAccessible grid s) (keepsStep grid s0 s (removeAccessible grid s) hk (removeStep grid s))
      (subTrans (removeAccessible grid s) s s0 (And.left (removeStep grid s)) hs)

theorem roundsInside (grid: Grid): (n: Nat) -> (s: Cells) -> Inside grid s -> Inside grid (rounds grid n s)
  | Zero,   s, ins => ins
  | Succ n, s, ins => roundsInside grid n (removeAccessible grid s) (removeInside grid s ins)

-- Enough rounds: a round with an accessible roll removes one, and once none
-- is accessible, rounds change nothing.

def accCount (grid: Grid) (s: Cells): Nat := countPositions grid (r c => accessible grid s r c)

theorem roundTerm: (b: Bool) -> (x: Cell) -> (b = True -> x = Roll) ->
    Bool.toNat ((if b then Floor else x) == Roll) + Bool.toNat b = Bool.toNat (x == Roll)
  | True,  x, hb => rewrite hb rfl
  | False, x, hb => Nat.addZero (Bool.toNat (x == Roll))

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
  | True,  h => Void.exfalso (Nat.succNotZero 0 h)

-- A count over positions that is 0 holds nowhere on the grid.
theorem countNone (grid: Grid) (p: Nat -> Nat -> Bool) (h: countPositions grid p = 0) (r: Nat) (c: Nat) (hr: r < grid.height) (hc: c < grid.width): p r c = False :=
  let sums := Eq.trans (Eq.sym (countPositionsSum grid p)) h
  let row := List.sumRangeZero (x => List.sumBy (y => Bool.toNat (p x y)) (List.range grid.width)) grid.height 0 sums r (Nat.zeroLe r) hr
  toNatZero (p r c) (List.sumRangeZero (y => Bool.toNat (p r y)) grid.width 0 row c (Nat.zeroLe c) hc)

-- Off the grid or not a roll: nothing to check.
theorem stableWhere (grid: Grid) (s: Cells) (ins: Inside grid s) (good: (r: Nat) -> (c: Nat) -> r < grid.height -> c < grid.width -> s r c = Roll -> 4 <= neighbours grid s r c):
    Stable grid s :=
  r c hs =>
    match e1: Nat.leq (Succ r) grid.height, e2: Nat.leq (Succ c) grid.width with
      | True,  True  => good r c e1 e2 hs
      | False, b     => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym (And.left ins r c (Nat.leqFalse (Succ r) grid.height e1))) hs))
      | True,  False => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym (And.right ins r c (Nat.leqFalse (Succ c) grid.width e2))) hs))

-- A roll that isn't accessible has at least 4 neighbours.
theorem andTrueLeft: (a: Bool) -> (b: Bool) -> a = True -> (a && b) = False -> b = False
  | True,  b, ha, h => h
  | False, b, ha, h => Void.exfalso (Bool.falseNotTrue ha)

theorem rollIsRoll (x: Cell) (h: x = Roll): (x == Roll) = True := rewrite h in rfl

theorem notAccessible (grid: Grid) (s: Cells) (r: Nat) (c: Nat) (h: accessible grid s r c = False) (hs: s r c = Roll): 4 <= neighbours grid s r c :=
  let few: Nat.leq (Succ (neighbours grid s r c)) 4 = False :=
    Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (Succ (neighbours grid s r c)) 4)))
      (andTrueLeft (s r c == Roll) (neighbours grid s r c < 4) (rollIsRoll (s r c) hs) h)
  Nat.leqFalse (Succ (neighbours grid s r c)) 4 few

-- No accessible roll: stable.
theorem noneStable (grid: Grid) (s: Cells) (ins: Inside grid s) (h: accCount grid s = 0): Stable grid s :=
  stableWhere grid s ins (r c hr hc hs => notAccessible grid s r c (countNone grid (r c => accessible grid s r c) h r c hr hc) hs)

theorem stableNotAccessible (grid: Grid) (s: Cells) (stable: Stable grid s) (r: Nat) (c: Nat): accessible grid s r c = False :=
  match e: s r c with
    | Floor => rfl
    | Roll  => Eq.trans (Bool.decTrueToBool (Nat.leq (Succ (neighbours grid s r c)) 4)) (Nat.leqFalseOfLess 4 (Succ (neighbours grid s r c)) (stable r c e))

-- Once stable, rounds change nothing.
theorem roundsFixed (grid: Grid): (n: Nat) -> (s: Cells) -> Stable grid s -> Same (rounds grid n s) s
  | Zero,   s, stable, r, c => rfl
  | Succ n, s, stable, r, c =>
    let same: Same (removeAccessible grid s) s := x y => rewrite stableNotAccessible grid s stable x y in rfl
    Eq.trans (roundsSame grid n (removeAccessible grid s) s same r c) (roundsFixed grid n s stable r c)

-- As many rounds as there are rolls leave no accessible roll.
theorem roundsStable (grid: Grid): (fuel: Nat) -> (s: Cells) -> Inside grid s -> rollCount grid s <= fuel -> Stable grid (rounds grid fuel s)
  | Zero,   s, ins, h, r, c, hs =>
    stableWhere grid s ins (x y hx hy hxy =>
      Void.exfalso (Bool.trueNotFalse
        (Eq.trans (Eq.sym (rollIsRoll (s x y) hxy))
          (countNone grid (x y => s x y == Roll) (Nat.leAntisym (rollCount grid s) 0 h (Nat.zeroLe (rollCount grid s))) x y hx hy)))) r c hs
  | Succ n, s, ins, h, r, c, hs =>
    match e: accCount grid s with
      | Zero   =>
        let stable := noneStable grid s ins e
        stableSame grid s (rounds grid (Succ n) s) (x y => Eq.sym (roundsFixed grid (Succ n) s stable x y)) stable r c hs
      | Succ b =>
        let total: rollCount grid (removeAccessible grid s) + Succ b <= Succ n := rewrite <- e, roundCount grid s in h
        roundsStable grid n (removeAccessible grid s) (removeInside grid s ins)
          (Nat.leOfAddLe (rollCount grid (removeAccessible grid s)) b n (Nat.addSuccLeSucc (rollCount grid (removeAccessible grid s)) b n total)) r c hs
