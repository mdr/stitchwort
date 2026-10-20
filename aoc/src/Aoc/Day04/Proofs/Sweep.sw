-- One pass of the program's `sweep`, row by row (`sweepAt`), and the two
-- facts part 2 needs about it:
--   - a pass is a run of steps that each remove only accessible rolls, one
--     row at a time (`passKeeps`): row k is peeled seeing the rows above as
--     already swept and the rows below as they were (`mix`);
--   - the marks are sound (`invSweep`): a row whose mark and the next row's
--     mark are both unset can't lose a roll, so skipping it is safe, and
--     when a pass sets no mark, no roll is accessible (`settledStable`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (Eq)

-- The rows of a marked grid, and its cells.
def rowsOf (m: Marked w h): Vec (Vec Cell w) h := Vec.map Pair.fst m

def mcells (m: Marked w h): Cells := rowsCells (rowsOf m)

-- Row r (counted from 1) of a marked grid with its mark: a row of floor,
-- unmarked, above the first and past the last.
def entry (m: Marked w h) (r: Nat): (Vec Cell w, Bool) :=
  List.getOr (Vec.replicate w Floor, False) r (Cons (Vec.replicate w Floor, False) (Vec.toList m))

theorem fstEntry (m: Marked w h) (r: Nat): Pair.fst (entry m r) = rowB (rowsOf m) r :=
  rewrite Vec.toListMap Pair.fst m in
    Eq.sym (List.getOrMap Pair.fst (Vec.replicate w Floor, False) r (Cons (Vec.replicate w Floor, False) (Vec.toList m)))

theorem rowIsEntry (m: Marked w h) (r: Nat): RowIs (mcells m) r (Pair.fst (entry m r)) :=
  rewrite fstEntry m r in rowBIs (rowsOf m) r

theorem mcellsEntry (m: Marked w h) (r: Nat) (c: Nat): mcells m r c = List.getOr Floor c (Vec.toList (Pair.fst (entry m (Succ r)))) :=
  rewrite fstEntry m (Succ r) in rfl

theorem entryPast [w: Nat] [h: Nat] (m: Marked w h) (r: Nat) (hr: h <= r): entry m (Succ r) = (Vec.replicate w Floor, False) :=
  List.getOrPast (Vec.replicate w Floor, False) r (Vec.toList m) (rewrite Vec.lengthToList m in hr)

theorem mcellsInside (grid: Grid) (m: Marked grid.width grid.height): Inside grid (mcells m) :=
  Both (r c h => rowsCellsBelow (rowsOf m) r c h) (r c h => rowsCellsRight (rowsOf m) r c h)

-- `sweepRow`: kept, or peeled.

theorem sweepRowCases (a: Vec Cell w) (ac: Bool) (x: Vec Cell w) (b: Vec Cell w):
    (mv: Bool) -> (bm: Bool) -> Or (Pair.fst (sweepRow a ac x mv b bm) = x) (Pair.fst (sweepRow a ac x mv b bm) = peelRow a x b)
  | True,  bm    => Inr rfl
  | False, True  => Inr rfl
  | False, False =>
    match ac with
      | True  => Inr rfl
      | False => Inl rfl

theorem notFalse: (c: Bool) -> not c = False -> c = True
  | True,  h => rfl
  | False, h => Void.exfalso (Bool.trueNotFalse h)

theorem peelSame (a: Vec Cell w) (x: Vec Cell w) (b: Vec Cell w) (h: not (Vec.toList (peelRow a x b) == Vec.toList x) = False): peelRow a x b = x :=
  Vec.toListInjective (peelRow a x b) x (Decidable.toBoolSound _ (notFalse (Vec.toList (peelRow a x b) == Vec.toList x) h))

theorem selfEqTrue (x: Vec Cell w): (Vec.toList x == Vec.toList x) = True := Decidable.toBoolOf _ (rfl: Vec.toList x = Vec.toList x)

-- An unmarked row of a pass is the row it was.
theorem sweepRowSame (a: Vec Cell w) (ac: Bool) (x: Vec Cell w) (b: Vec Cell w): (mv: Bool) -> (bm: Bool) ->
    Pair.snd (sweepRow a ac x mv b bm) = False -> Pair.fst (sweepRow a ac x mv b bm) = x
  | True,  bm,    h => peelSame a x b h
  | False, True,  h => peelSame a x b h
  | False, False, h =>
    match ac with
      | True  => peelSame a x b h
      | False => rfl

-- A row a pass leaves as it was is unmarked.
theorem sweepRowMark (a: Vec Cell w) (ac: Bool) (x: Vec Cell w) (b: Vec Cell w): (mv: Bool) -> (bm: Bool) ->
    Pair.fst (sweepRow a ac x mv b bm) = x -> Pair.snd (sweepRow a ac x mv b bm) = False
  | True,  bm,    h => rewrite h, selfEqTrue x in rfl
  | False, True,  h => rewrite h, selfEqTrue x in rfl
  | False, False, h =>
    match ac with
      | True  => rewrite h, selfEqTrue x in rfl
      | False => rfl

-- An unmarked row whose own mark, the next row's and the row above's
-- change were all unset is peeled to itself when that was so already.
theorem peelOrSettled (a: Vec Cell w) (ac: Bool) (x: Vec Cell w) (b: Vec Cell w): (mv: Bool) -> (bm: Bool) ->
    Pair.snd (sweepRow a ac x mv b bm) = False -> (mv = False -> bm = False -> ac = False -> peelRow a x b = x) -> peelRow a x b = x
  | True,  bm,    h, skip => peelSame a x b h
  | False, True,  h, skip => peelSame a x b h
  | False, False, h, skip =>
    match e: ac with
      | True  => peelSame a x b h
      | False => skip rfl rfl rfl

-- One pass, row by row.

def stepAt (prev: (Vec Cell w, Bool)) (cur: (Vec Cell w, Bool)) (next: (Vec Cell w, Bool)): (Vec Cell w, Bool) :=
  let y := sweepRow (Pair.fst prev) (Pair.snd prev) (Pair.fst cur) (Pair.snd cur) (Pair.fst next) (Pair.snd next)
  (Pair.fst y, Pair.snd y)

theorem sweepFromAt [w: Nat] [h: Nat] (gap: Vec Cell w): (above: Vec Cell w) -> (ch: Bool) -> (m: Marked w h) -> (r: Nat) -> r < h ->
    List.getOr (gap, False) r (Vec.toList (sweepFrom gap above ch m))
      = stepAt (List.getOr (gap, False) r (Cons (above, ch) (Vec.toList (sweepFrom gap above ch m))))
          (List.getOr (gap, False) r (Vec.toList m)) (List.getOr (gap, False) (Succ r) (Vec.toList m))
  | above, ch, VNil,                          r,      hr => Void.exfalso (Bool.falseNotTrue hr)
  | above, ch, VCons (MkPair row moved) rest, Zero,   hr => rewrite Vec.headOrToList (gap, False) rest
  | above, ch, VCons (MkPair row moved) rest, Succ r, hr =>
    let y := sweepRow above ch row moved (Pair.fst (Vec.headOr (gap, False) rest)) (Pair.snd (Vec.headOr (gap, False) rest))
    sweepFromAt gap (Pair.fst y) (Pair.snd y) rest r hr

-- Row r after a pass: from the swept row above it, and the row and the
-- row below as they were.
theorem sweepAt [w: Nat] [h: Nat] (m: Marked w h) (r: Nat) (hr: r < h): entry (sweep m) (Succ r) = stepAt (entry (sweep m) r) (entry m (Succ r)) (entry m (Succ (Succ r))) :=
  sweepFromAt (Vec.replicate w Floor) (Vec.replicate w Floor) False m r hr

-- An unmarked row of a pass is the row it was.
theorem unchanged (m: Marked w h) (j: Nat) (hm: Pair.snd (entry (sweep m) (Succ j)) = False): Pair.fst (entry (sweep m) (Succ j)) = Pair.fst (entry m (Succ j)) :=
  match e: Nat.leq (Succ j) h with
    | True  =>
      let st := sweepAt m j e
      let p := entry (sweep m) j
      let x := entry m (Succ j)
      let n := entry m (Succ (Succ j))
      Eq.trans (Eq.cong Pair.fst st)
        (sweepRowSame (Pair.fst p) (Pair.snd p) (Pair.fst x) (Pair.fst n) (Pair.snd x) (Pair.snd n) (Eq.trans (Eq.cong Pair.snd (Eq.sym st)) hm))
    | False => rewrite entryPast (sweep m) j (Nat.leqFalse (Succ j) h e), entryPast m j (Nat.leqFalse (Succ j) h e)

theorem prevSame (m: Marked w h): (r: Nat) -> Pair.snd (entry (sweep m) r) = False -> Pair.fst (entry (sweep m) r) = Pair.fst (entry m r)
  | Zero,   hm => rfl
  | Succ j, hm => unchanged m j hm

-- The marks are sound.

-- Row r (counted from 0) is as peeling it would leave it.
def Settled (m: Marked w h) (r: Nat): Prop :=
  peelRow (Pair.fst (entry m r)) (Pair.fst (entry m (Succ r))) (Pair.fst (entry m (Succ (Succ r)))) = Pair.fst (entry m (Succ r))

-- A row whose mark and the next row's are unset is settled.
def Inv (m: Marked w h): Prop :=
  (r: Nat) -> r < h -> Pair.snd (entry m (Succ r)) = False -> Pair.snd (entry m (Succ (Succ r))) = False -> Settled m r

theorem invSweep (m: Marked w h) (inv: Inv m): Inv (sweep m) :=
  r hr h1 h2 =>
    let st := sweepAt m r hr
    let p := entry (sweep m) r
    let x := entry m (Succ r)
    let n := entry m (Succ (Succ r))
    let quiet: Pair.snd (sweepRow (Pair.fst p) (Pair.snd p) (Pair.fst x) (Pair.snd x) (Pair.fst n) (Pair.snd n)) = False :=
      Eq.trans (Eq.cong Pair.snd (Eq.sym st)) h1
    rewrite unchanged m r h1, unchanged m (Succ r) h2 in
      peelOrSettled (Pair.fst p) (Pair.snd p) (Pair.fst x) (Pair.fst n) (Pair.snd x) (Pair.snd n) quiet
        (e1 e2 e3 => rewrite prevSame m r e3 in inv r hr e1 e2)

-- A pass is a run of steps, one row at a time.

-- The cells after rows 0 to k - 1 of a pass: those rows as `out` has
-- them, the rest as `inp` has them.
def mix (k: Nat) (out: Cells) (inp: Cells): Cells := r c => if Nat.leq (Succ r) k then out r c else inp r c

theorem mixBelow (k: Nat) (out: Cells) (inp: Cells) (r: Nat) (c: Nat) (h: r < k): mix k out inp r c = out r c := rewrite h in rfl

theorem mixAbove (k: Nat) (out: Cells) (inp: Cells) (r: Nat) (c: Nat) (h: k <= r): mix k out inp r c = inp r c :=
  rewrite Nat.leqFalseOfLess k (Succ r) h in rfl

theorem ifBoth: (b: Bool) -> (x: Cell) -> (y: Cell) -> x = Floor -> y = Floor -> (if b then x else y) = Floor
  | True,  x, y, hx, hy => hx
  | False, x, y, hx, hy => hy

theorem mixInside (grid: Grid) (k: Nat) (out: Cells) (inp: Cells) (io: Inside grid out) (ii: Inside grid inp): Inside grid (mix k out inp) :=
  Both (r c h => ifBoth (Nat.leq (Succ r) k) (out r c) (inp r c) (And.left io r c h) (And.left ii r c h))
    (r c h => ifBoth (Nat.leq (Succ r) k) (out r c) (inp r c) (And.right io r c h) (And.right ii r c h))

theorem keepRoll: (a: Cell) -> (w: Nat) -> keep a w = Roll -> a = Roll
  | Roll,  w, h => rfl
  | Floor, w, h => Void.exfalso (rollNotFloor h)

-- A roll a round removes has fewer than 5 rolls in its window.
theorem keepFloor: (w: Nat) -> keep Roll w = Floor -> w < 5
  | 0,                                  h => rfl
  | 1,                                  h => rfl
  | 2,                                  h => rfl
  | 3,                                  h => rfl
  | 4,                                  h => rfl
  | Succ (Succ (Succ (Succ (Succ n)))), h => Void.exfalso (rollNotFloor (Eq.sym h))

-- A roll a round keeps has at least 5.
theorem keepRollGe: (w: Nat) -> keep Roll w = Roll -> 5 <= w
  | 0,                                  h => Void.exfalso (rollNotFloor h)
  | 1,                                  h => Void.exfalso (rollNotFloor h)
  | 2,                                  h => Void.exfalso (rollNotFloor h)
  | 3,                                  h => Void.exfalso (rollNotFloor h)
  | 4,                                  h => Void.exfalso (rollNotFloor h)
  | Succ (Succ (Succ (Succ (Succ n)))), h => rfl

-- Changing row k only, each cell either kept or as a round leaves it, is a step.
theorem rowStep (grid: Grid) (s: Cells) (t: Cells) (ins: Inside grid s) (k: Nat)
    (others: (r: Nat) -> (c: Nat) -> Not (r = k) -> t r c = s r c)
    (row: (c: Nat) -> Or (t k c = s k c) (t k c = keep (s k c) (window s k c))): Step grid s t :=
  let rowSub: (c: Nat) -> t k c = Roll -> s k c = Roll := c ht =>
    match row c with
      | Inl e => Eq.trans (Eq.sym e) ht
      | Inr e => keepRoll (s k c) (window s k c) (Eq.trans (Eq.sym e) ht)
  let rowFew: (c: Nat) -> s k c = Roll -> t k c = Floor -> neighbours grid s k c < 4 := c hs ht =>
    match row c with
      | Inl e => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym ht) (Eq.trans e hs)))
      | Inr e =>
        let n := neighbours grid s k c
        let few: window s k c < 5 :=
          keepFloor (window s k c) (Eq.trans (Eq.cong (a => keep a (window s k c)) (Eq.sym hs)) (Eq.trans (Eq.sym e) ht))
        let few2: n + (s k c).count < 5 := Nat.ltCongLeft (window s k c) (n + (s k c).count) 5 (windowIsNeighbours grid s (And.left ins) (And.right ins) k c) few
        let few3: n + 1 < 5 := Nat.ltCongLeft (n + (s k c).count) (n + 1) 5 (Eq.cong ((a: Cell) => n + a.count) hs) few2
        Nat.ltCongLeft (n + 1) (Succ n) 5 (Nat.addOne n) few3
  Both
    (r c ht =>
      match Nat.decEq r k with
        | Yes p => rewrite p in rowSub c (rewrite <- p in ht)
        | No q  => Eq.trans (Eq.sym (others r c q)) ht)
    (r c hs ht =>
      match Nat.decEq r k with
        | Yes p => rewrite p in rowFew c (rewrite <- p in hs) (rewrite <- p in ht)
        | No q  => Void.exfalso (rollNotFloor (Eq.trans (Eq.sym ht) (Eq.trans (others r c q) hs))))

-- The border rows of `mix k`: rows above k as swept, the rest as they were.
theorem bordMixOut (k: Nat) (out: Cells) (inp: Cells) (r: Nat) (h: r < k): (j: Nat) -> bord out (Succ r) j = bord (mix k out inp) (Succ r) j
  | Zero   => rfl
  | Succ c => Eq.sym (mixBelow k out inp r c h)

theorem bordMixIn (k: Nat) (out: Cells) (inp: Cells) (r: Nat) (h: k <= r): (j: Nat) -> bord inp (Succ r) j = bord (mix k out inp) (Succ r) j
  | Zero   => rfl
  | Succ c => Eq.sym (mixAbove k out inp r c h)

theorem bordMixPrev (out: Cells) (inp: Cells): (k: Nat) -> (j: Nat) -> bord out k j = bord (mix k out inp) k j
  | Zero,   j => rfl
  | Succ r, j => bordMixOut (Succ r) out inp r (Nat.leRefl r) j

theorem rowIsMove (cells: Cells) (other: Cells) (r: Nat) (v: Vec Cell w) (hv: RowIs cells r v) (same: (j: Nat) -> bord cells r j = bord other r j): RowIs other r v :=
  j => Eq.trans (hv j) (same j)

-- Row k of a pass, from `mix k`: kept, or as a round leaves it.
theorem passRow (grid: Grid) (m: Marked grid.width grid.height) (k: Nat) (hk: k < grid.height) (c: Nat):
    Or (mcells (sweep m) k c = mcells m k c) (mcells (sweep m) k c = keep (mcells m k c) (window (mix k (mcells (sweep m)) (mcells m)) k c)) :=
  let out := mcells (sweep m)
  let inp := mcells m
  let s := mix k out inp
  let st := sweepAt m k hk
  let p := entry (sweep m) k
  let x := entry m (Succ k)
  let n := entry m (Succ (Succ k))
  let y := sweepRow (Pair.fst p) (Pair.snd p) (Pair.fst x) (Pair.snd x) (Pair.fst n) (Pair.snd n)
  let rowOut: mcells (sweep m) k c = List.getOr Floor c (Vec.toList (Pair.fst y)) :=
    Eq.trans (mcellsEntry (sweep m) k c) (Eq.cong (v => List.getOr Floor c (Vec.toList (Pair.fst v))) st)
  match sweepRowCases (Pair.fst p) (Pair.snd p) (Pair.fst x) (Pair.fst n) (Pair.snd x) (Pair.snd n) with
    | Inl e => Inl (Eq.trans rowOut (rewrite e in Eq.sym (mcellsEntry m k c)))
    | Inr e =>
      let ha: RowIs s k (Pair.fst p) := rowIsMove out s k (Pair.fst p) (rowIsEntry (sweep m) k) (j => bordMixPrev out inp k j)
      let hx: RowIs s (Succ k) (Pair.fst x) := rowIsMove inp s (Succ k) (Pair.fst x) (rowIsEntry m (Succ k)) (j => bordMixIn k out inp k (Nat.leRefl k) j)
      let hn: RowIs s (Succ (Succ k)) (Pair.fst n) := rowIsMove inp s (Succ (Succ k)) (Pair.fst n) (rowIsEntry m (Succ (Succ k))) (j => bordMixIn k out inp (Succ k) (Nat.leSucc k) j)
      Inr (calc mcells (sweep m) k c
        _ = List.getOr Floor c (Vec.toList (peelRow (Pair.fst p) (Pair.fst x) (Pair.fst n))) := rewrite <- e in rowOut
        _ = keep (s k c) (window s k c) := peelRowCells s k c (Pair.fst p) (Pair.fst x) (Pair.fst n) ha hx hn
        _ = keep (inp k c) (window s k c) := rewrite mixAbove k out inp k c (Nat.leRefl k))

-- Rows 0 to k - 1 swept to rows 0 to k: a step.
theorem mixStep (grid: Grid) (m: Marked grid.width grid.height) (k: Nat) (hk: k < grid.height):
    Step grid (mix k (mcells (sweep m)) (mcells m)) (mix (Succ k) (mcells (sweep m)) (mcells m)) :=
  let out := mcells (sweep m)
  let inp := mcells m
  rowStep grid (mix k out inp) (mix (Succ k) out inp) (mixInside grid k out inp (mcellsInside grid (sweep m)) (mcellsInside grid m)) k
    (r c ne =>
      match e: Nat.leq (Succ r) k with
        | True  => mixBelow (Succ k) out inp r c (Nat.leTrans (Succ r) k (Succ k) e (Nat.leSucc k))
        | False => mixAbove (Succ k) out inp r c (Nat.leNeSucc k r (Nat.leqFalse (Succ r) k e) (q => ne (Eq.sym q))))
    (c =>
      let now := mixBelow (Succ k) out inp k c (Nat.leRefl k)
      let before := mixAbove k out inp k c (Nat.leRefl k)
      match passRow grid m k hk c with
        | Inl e => Inl (Eq.trans now (Eq.trans e (Eq.sym before)))
        | Inr e => Inr (Eq.trans now (Eq.trans e (Eq.cong ((a: Cell) => keep a (window (mix k out inp) k c)) (Eq.sym before)))))

-- A pass keeps the stable sets and only removes rolls.
theorem mixChain (grid: Grid) (s0: Cells) (m: Marked grid.width grid.height) (hk: Keeps grid s0 (mcells m)):
    (k: Nat) -> k <= grid.height -> And (Keeps grid s0 (mix k (mcells (sweep m)) (mcells m))) (Sub (mix k (mcells (sweep m)) (mcells m)) (mcells m))
  | Zero,   h => Both hk (subRefl (mcells m))
  | Succ k, h =>
    let out := mcells (sweep m)
    let inp := mcells m
    let prev := mixChain grid s0 m hk k (Nat.leTrans k (Succ k) grid.height (Nat.leSucc k) h)
    let step := mixStep grid m k h
    Both (keepsStep grid s0 (mix k out inp) (mix (Succ k) out inp) (And.left prev) step)
      (subTrans (mix (Succ k) out inp) (mix k out inp) inp (And.left step) (And.right prev))

theorem passKeeps (grid: Grid) (s0: Cells) (m: Marked grid.width grid.height) (hk: Keeps grid s0 (mcells m)):
    And (Keeps grid s0 (mcells (sweep m))) (Sub (mcells (sweep m)) (mcells m)) :=
  let out := mcells (sweep m)
  let inp := mcells m
  let chain := mixChain grid s0 m hk grid.height (Nat.leRefl grid.height)
  let same: Same out (mix grid.height out inp) := r c =>
    match e: Nat.leq (Succ r) grid.height with
      | True  => rfl
      | False =>
        let past := Nat.leqFalse (Succ r) grid.height e
        Eq.trans (And.left (mcellsInside grid (sweep m)) r c past) (Eq.sym (And.left (mcellsInside grid m) r c past))
  Both (k st sub r c hk2 => Eq.trans (same r c) (And.left chain k st sub r c hk2))
    (r c ho => And.right chain r c (Eq.trans (Eq.sym (same r c)) ho))

-- When every row is settled, every roll has at least 4 neighbours.
theorem settledStable (grid: Grid) (m: Marked grid.width grid.height) (inv: Inv m) (none: (r: Nat) -> Pair.snd (entry m (Succ r)) = False): Stable grid (mcells m) :=
  stableWhere grid (mcells m) (mcellsInside grid m) (r c hr hc hs =>
    let cells := mcells m
    let w := window cells r c
    let n := neighbours grid cells r c
    let same: keep (cells r c) w = cells r c :=
      calc keep (cells r c) w
        _ = List.getOr Floor c (Vec.toList (peelRow (Pair.fst (entry m r)) (Pair.fst (entry m (Succ r))) (Pair.fst (entry m (Succ (Succ r))))))
            := Eq.sym (peelRowCells cells r c (Pair.fst (entry m r)) (Pair.fst (entry m (Succ r))) (Pair.fst (entry m (Succ (Succ r))))
                 (rowIsEntry m r) (rowIsEntry m (Succ r)) (rowIsEntry m (Succ (Succ r))))
        _ = List.getOr Floor c (Vec.toList (Pair.fst (entry m (Succ r)))) := rewrite inv r hr (none r) (none (Succ r))
        _ = cells r c := Eq.sym (mcellsEntry m r c)
    let kept: keep Roll w = Roll := Eq.trans (Eq.cong (a => keep a w) (Eq.sym hs)) (Eq.trans same hs)
    let many: 5 <= n + (cells r c).count :=
      Nat.leCongRight 5 w (n + (cells r c).count) (windowIsNeighbours grid cells (And.left (mcellsInside grid m)) (And.right (mcellsInside grid m)) r c) (keepRollGe w kept)
    let many2: 5 <= n + 1 := Nat.leCongRight 5 (n + (cells r c).count) (n + 1) (Eq.cong ((a: Cell) => n + a.count) hs) many
    Nat.leCongRight 5 (n + 1) (Succ n) (Nat.addOne n) many2)
