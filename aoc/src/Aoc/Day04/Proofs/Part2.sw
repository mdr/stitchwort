-- Day 4, part 2 proved for every grid: the printed answer is the number of
-- rolls the puzzle's rounds remove, as Proofs/Spec.sw states it
-- (`part2Correct`, at the bottom). The program sweeps instead of running
-- rounds; both are processes that remove only accessible rolls and stop
-- when none is accessible, so both end at the grid's core (Proofs/Core.sw).
-- For the sweep: each pass is such a process (`passKeeps`, Proofs/Sweep.sw);
-- the marks are sound, so a pass that marks nothing leaves no accessible
-- roll (`invSweep`, `settledStable`); and a pass that marks something
-- removes a roll (`fewerRolls`), so the sweep, which goes on while the rolls
-- left decrease, ends with all marks clear (`settleEnds`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (And, Bool, Eq, List, Nat, Pair, Vec, Void)

-- Counting rolls.

theorem countMono (grid: Grid) (t: Cells) (s: Cells) (h: Sub t s): rollCount grid t <= rollCount grid s :=
  rewrite countPositionsSum grid (r c => t r c == Roll), countPositionsSum grid (r c => s r c == Roll) in
    List.sumByLe (x => List.sumBy (y => Bool.toNat (s x y == Roll)) (List.range grid.width)) (x => List.sumBy (y => Bool.toNat (t x y == Roll)) (List.range grid.width))
      (x => List.sumByLe (y => Bool.toNat (s x y == Roll)) (y => Bool.toNat (t x y == Roll)) (y => termLe True (t x y) (s x y) (h x y)) (List.range grid.width))
      (List.range grid.height)

theorem subZeroLe: (n: Nat) -> (m: Nat) -> n - m = 0 -> n <= m
  | Zero,   m,      h => rfl
  | Succ n, Zero,   h => Void.exfalso omega
  | Succ n, Succ m, h => subZeroLe n m h

-- Equal sums of terms each at most the other's: equal terms.
theorem sumEqEach (f: Nat -> Nat) (g: Nat -> Nat) (le: (x: Nat) -> g x <= f x) (n: Nat)
    (eq: List.sumBy g (List.range n) = List.sumBy f (List.range n)) (x: Nat) (hx: x < n): g x = f x :=
  let split := List.sumBySplit f g le (List.range n)
  let rest: List.sumBy (y => f y - g y) (List.range n) = 0 :=
    omega [split]
  omega [le x, subZeroLe (f x) (g x) (List.sumRangeZero (y => f y - g y) n 0 rest x omega hx)]

theorem cellOfToNat: (a: Cell) -> (b: Cell) -> Bool.toNat (a == Roll) = Bool.toNat (b == Roll) -> a = b
  | Roll,  Roll,  h => rfl
  | Floor, Floor, h => rfl
  | Roll,  Floor, h => Void.exfalso omega
  | Floor, Roll,  h => Void.exfalso omega

-- Off the grid both are floor: only the grid's positions need checking.
theorem sameWhere (grid: Grid) (s: Cells) (t: Cells) (is: Inside grid s) (it: Inside grid t)
    (good: (r: Nat) -> (c: Nat) -> r < grid.height -> c < grid.width -> s r c = t r c): Same s t :=
  r c =>
    match e1: Nat.leq (Succ r) grid.height, e2: Nat.leq (Succ c) grid.width with
      | True,  True  => good r c e1 e2
      | False, b     => Eq.trans (And.left is r c omega) (Eq.sym (And.left it r c omega))
      | True,  False => Eq.trans (And.right is r c omega) (Eq.sym (And.right it r c omega))

-- Removing rolls without changing the count removes none.
theorem countEqSame (grid: Grid) (t: Cells) (s: Cells) (it: Inside grid t) (is: Inside grid s) (h: Sub t s) (eq: rollCount grid t = rollCount grid s): Same t s :=
  let rowT := (x: Nat) => List.sumBy (y => Bool.toNat (t x y == Roll)) (List.range grid.width)
  let rowS := (x: Nat) => List.sumBy (y => Bool.toNat (s x y == Roll)) (List.range grid.width)
  let rowLe := (x: Nat) => List.sumByLe (y => Bool.toNat (s x y == Roll)) (y => Bool.toNat (t x y == Roll)) (y => termLe True (t x y) (s x y) (h x y)) (List.range grid.width)
  let sums: List.sumBy rowT (List.range grid.height) = List.sumBy rowS (List.range grid.height) :=
    Eq.trans (Eq.sym (countPositionsSum grid (r c => t r c == Roll))) (Eq.trans eq (countPositionsSum grid (r c => s r c == Roll)))
  sameWhere grid t s it is (r c hr hc =>
    cellOfToNat (t r c) (s r c)
      (sumEqEach (y => Bool.toNat (s r y == Roll)) (y => Bool.toNat (t r y == Roll)) (y => termLe True (t r y) (s r y) (h r y)) grid.width
        (sumEqEach rowS rowT rowLe grid.height sums r hr) c hc))

theorem emptyStable (grid: Grid) (s: Cells) (ins: Inside grid s) (h: rollCount grid s = 0): Stable grid s :=
  stableWhere grid s ins (x y hx hy hxy =>
    Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (rollIsRoll (s x y) hxy)) (countNone grid (x y => s x y == Roll) h x y hx hy))))

-- A pass that changes nothing leaves no mark.

theorem rowExt (u: Vec Cell w) (v: Vec Cell w) (h: (c: Nat) -> List.getOr Floor c (Vec.toList u) = List.getOr Floor c (Vec.toList v)): u = v :=
  Vec.toListInjective u v
    (List.extGetOr Floor (Vec.toList u) (Vec.toList v) (rewrite Vec.lengthToList u, Vec.lengthToList v in rfl) (i hi => h i))

theorem sameMarks (grid: Grid) (m: Marked grid.width grid.height) (same: Same (mcells (sweep m)) (mcells m)) (r: Nat): Pair.snd (entry (sweep m) (Succ r)) = False :=
  match e: Nat.leq (Succ r) grid.height with
    | True  =>
      let st := sweepAt m r e
      let p := entry (sweep m) r
      let x := entry m (Succ r)
      let n := entry m (Succ (Succ r))
      let rowEq: Pair.fst (entry (sweep m) (Succ r)) = x.fst :=
        rowExt (Pair.fst (entry (sweep m) (Succ r))) x.fst
          (c => Eq.trans (Eq.sym (mcellsEntry (sweep m) r c)) (Eq.trans (same r c) (mcellsEntry m r c)))
      Eq.trans (Eq.cong Pair.snd st)
        (sweepRowMark p.fst p.snd x.fst n.fst x.snd n.snd (Eq.trans (Eq.cong Pair.fst (Eq.sym st)) rowEq))
    | False => rewrite entryPast (sweep m) r omega

theorem ifTrueFalse: (b: Bool) -> (c: Bool) -> (if b then True else c) = False -> (b = False && c = False)
  | True,  c, h => Void.exfalso (Bool.trueNotFalse h)
  | False, c, h => Both rfl h

theorem ifFalseFalse: (b: Bool) -> (c: Bool) -> b = False -> c = False -> (if b then True else c) = False
  | False, c, hb, hc => hc
  | True,  c, hb, hc => Void.exfalso (Bool.trueNotFalse hb)

-- `any` says no element holds when none does, and the other way round.
theorem anyNone (p: a -> Bool) (d: a) (hd: p d = False): (xs: List a) -> List.any p xs = False -> (i: Nat) -> p (List.getOr d i xs) = False
  | Nil,       h, i      => hd
  | Cons x xs, h, Zero   => And.left (ifTrueFalse (p x) (List.any p xs) h)
  | Cons x xs, h, Succ i => anyNone p d hd xs (And.right (ifTrueFalse (p x) (List.any p xs) h)) i

theorem anyAll (p: a -> Bool) (d: a): (xs: List a) -> ((i: Nat) -> p (List.getOr d i xs) = False) -> List.any p xs = False
  | Nil,       h => rfl
  | Cons x xs, h => ifFalseFalse (p x) (List.any p xs) (h 0) (anyAll p d xs (i => h (Succ i)))

theorem marksNone (m: Marked w h) (none: Vec.any Pair.snd m = False) (r: Nat): Pair.snd (entry m (Succ r)) = False :=
  anyNone Pair.snd (Vec.replicate w Floor, False) rfl (Vec.toList m) (Eq.trans (Eq.sym (Vec.anyToList Pair.snd m)) none) r

theorem marksAll (m: Marked w h) (none: (r: Nat) -> Pair.snd (entry m (Succ r)) = False): Vec.any Pair.snd m = False :=
  Eq.trans (Vec.anyToList Pair.snd m) (anyAll Pair.snd (Vec.replicate w Floor, False) (Vec.toList m) none)

-- A pass that marks a row removes a roll.
theorem fewerRolls (grid: Grid) (s0: Cells) (m: Marked grid.width grid.height) (hk: Keeps grid s0 (mcells m)) (marked: Vec.any Pair.snd (sweep m) = True):
    rollCount grid (mcells (sweep m)) < rollCount grid (mcells m) :=
  let sub := And.right (passKeeps grid s0 m hk)
  Nat.leNeSucc (rollCount grid (mcells (sweep m))) (rollCount grid (mcells m)) (countMono grid (mcells (sweep m)) (mcells m) sub)
    (eq =>
      let same := countEqSame grid (mcells (sweep m)) (mcells m) (mcellsInside grid (sweep m)) (mcellsInside grid m) sub eq
      Bool.trueNotFalse (Eq.trans (Eq.sym marked) (marksAll (sweep m) (sameMarks grid m same))))

-- The start: every row marked.

theorem fstPairs: (rows: Vec (Vec Cell w) h) -> Vec.map Pair.fst (Vec.map (row => (row, True)) rows) = rows
  | VNil       => rfl
  | VCons x xs => Eq.cong (VCons x) (fstPairs xs)

theorem marksTrue (gap: Vec Cell w): (rows: Vec (Vec Cell w) h) -> (r: Nat) -> r < h ->
    Pair.snd (List.getOr (gap, False) r (Vec.toList (Vec.map (row => (row, True)) rows))) = True
  | VNil,       r,      hr => Void.exfalso (Bool.falseNotTrue hr)
  | VCons x xs, Zero,   hr => rfl
  | VCons x xs, Succ r, hr => marksTrue gap xs r hr

theorem startInv (rows: Vec (Vec Cell w) h): Inv (Vec.map (row => (row, True)) rows) :=
  r hr h1 h2 => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym (marksTrue (Vec.replicate w Floor) rows r hr)) h1))

theorem startCells (grid: Grid): Same (mcells (Vec.map (row => (row, True)) grid.rows)) (cellsOf grid) :=
  r c => rewrite fstPairs grid.rows in rfl

-- The rolls of the program's grid are the spec's.
theorem rollsIsCount (grid: Grid) (rows: Vec (Vec Cell grid.width) grid.height):
    Vec.sumBy (row => Vec.sumBy Cell.count row) rows = rollCount grid (rowsCells rows) :=
  Eq.trans (rollsCells rows)
    (Eq.trans
      (List.sumByCong (r => List.sumBy (c => (rowsCells rows r c).count) (List.range grid.width)) (r => List.sumBy (c => Bool.toNat (rowsCells rows r c == Roll)) (List.range grid.width))
        (List.range grid.height)
        (r => List.sumByCong (c => (rowsCells rows r c).count) (c => Bool.toNat (rowsCells rows r c == Roll)) (List.range grid.width) (c => Eq.sym (isRollCount (rowsCells rows r c)))))
      (Eq.sym (countPositionsSum grid (r c => rowsCells rows r c == Roll))))
-- The program's measure is the rolls the spec counts.
theorem markedRolls (grid: Grid) (m: Marked grid.width grid.height): Marked.rolls m = rollCount grid (mcells m) :=
  rollsIsCount grid (rowsOf m)

-- One step of `settleMarked`: another pass when it removes a roll, else done.
theorem settleMore (m: Marked w h) (fewer: Nat.leq (Succ (Marked.rolls (sweep m))) (Marked.rolls m) = True): settleMarked m = settleMarked (sweep m) :=
  rewrite settleMarked.unfold m in
  rewrite fewer in
  rfl

theorem settleDone (m: Marked w h) (done: Nat.leq (Succ (Marked.rolls (sweep m))) (Marked.rolls m) = False): settleMarked m = sweep m :=
  rewrite settleMarked.unfold m in
  rewrite done in
  rfl

-- Sweeping until a pass removes no roll ends with no accessible roll, having
-- kept every stable set.
theorem settleEnds (grid: Grid) (s0: Cells) (m: Marked grid.width grid.height) (inv: Inv m) (hk: Keeps grid s0 (mcells m)) (hs: Sub (mcells m) s0):
    Stable grid (mcells (settleMarked m)) && (Keeps grid s0 (mcells (settleMarked m)) && Sub (mcells (settleMarked m)) s0)
  decreasing Marked.rolls m
:=
  let next := sweep m
  let pass := passKeeps grid s0 m hk
  let hs2 := subTrans (mcells next) (mcells m) s0 (And.right pass) hs
  match e: Nat.leq (Succ (Marked.rolls next)) (Marked.rolls m) with
    | True  =>
      rewrite settleMore m e in
      settleEnds grid s0 next (invSweep m inv) (And.left pass) hs2 [decreasing := e]
    | False =>
      rewrite settleDone m e in
      match a: Vec.any Pair.snd next with
        | False => Both (settledStable grid next (invSweep m inv) (marksNone next a)) (Both (And.left pass) hs2)
        | True  =>
          let fewer: Nat.leq (Succ (Marked.rolls next)) (Marked.rolls m) = True :=
            rewrite markedRolls grid next, markedRolls grid m in fewerRolls grid s0 m hk a
          Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym fewer) e))


-- Part 2 is right for every grid: the printed answer is the number of rolls
-- the puzzle's rounds remove.
theorem part2Correct (grid: Grid): solvePart2 grid = part2Spec grid :=
  let s0 := cellsOf grid
  let m0 := Vec.map (row => (row, True)) grid.rows
  let start := rollCount grid s0
  let same0 := startCells grid
  let keeps0: Keeps grid s0 (mcells m0) := k st sub r c hk => Eq.trans (same0 r c) (sub r c hk)
  let sub0: Sub (mcells m0) s0 := r c h => Eq.trans (Eq.sym (same0 r c)) h
  let ends := settleEnds grid s0 m0 (startInv grid.rows) keeps0 sub0
  let f := settleMarked m0
  let spec := rounds grid start s0
  let specKeep := roundsKeep grid s0 start s0 (k st sub => sub) (subRefl s0)
  let specStable := roundsStable grid start s0 (insideGrid grid) (Nat.leRefl start)
  let same := endsAgree grid s0 (mcells f) spec (And.right (And.right ends)) (And.left ends) (And.left (And.right ends))
    (And.right specKeep) specStable (And.left specKeep)
  calc solvePart2 grid
    _ = start - rollCount grid (mcells f)
        := Eq.trans (Eq.cong (t => t - Vec.sumBy (row => Vec.sumBy Cell.count row) (rowsOf f)) (rollsIsCount grid grid.rows))
             (Eq.cong (t => start - t) (rollsIsCount grid (rowsOf f)))
    _ = start - rollCount grid spec := rewrite rollCountSame grid (mcells f) spec same
    _ = part2Spec grid
