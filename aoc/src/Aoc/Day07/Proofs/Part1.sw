-- Day 7, part 1, proved for every manifold (`part1Correct`, at the bottom):
-- the program's count is the number of splitters some timeline of
-- Proofs/Spec.sw reaches. The argument:
--   1. `reach ls c k d`: a particle falling into column c of the first of
--      the rows `ls` can fall into column d of row k. A timeline reaches the
--      splitter in row k, column d exactly when there is a splitter there and
--      the particle can fall into it (`hitsAt`), by induction on the rows.
--   2. The program carries a row of beam flags down. A beam is in column d
--      of row k when the particle can fall there from some column with a
--      beam at the start (`beamReach`). One row of `fall` keeps this true
--      (`fallKeeps`): a beam passes a column without a splitter, and a
--      splitter with a beam sends one down each side, which are exactly the
--      particle's next columns. The flags stop at the manifold's edges,
--      which lose nothing: past the right edge there are no splitters, so a
--      particle there never comes back (`reachPast`), and left of the left
--      edge a timeline ends.
--   3. So the splitters a row's beams reach are the splitters the particle
--      reaches in that row (`splitsBelowSum`).

namespace Aoc.Day07.Proofs
import Aoc.Day07 (..)
import Std (Bool, DecEq, Eq, Fin, List, Nat, Option, Vec, Void)

-- Bool and list facts --------------------------------------------------------

theorem orCases (goal: Prop): (a: Bool) -> (b: Bool) -> (a || b) = True -> (a = True -> goal) -> (b = True -> goal) -> goal
  | True,  b, h, f, g => f rfl
  | False, b, h, f, g => g h

theorem andOr: (a: Bool) -> (x: Bool) -> (y: Bool) -> ((a && x) || (a && y)) = (a && (x || y))
  | True,  x, y => rfl
  | False, x, y => rfl

theorem notTrue: (a: Bool) -> Bool.not a = True -> a = False
  | False, h => rfl
  | True,  h => Void.exfalso (Bool.falseNotTrue h)

theorem natEqSelf (n: Nat): (n == n) = True := rewrite Nat.eqIsEqual n n in Nat.equalRefl n

theorem natEqBelow (m: Nat) (n: Nat) (h: m < n): (m == n) = False :=
  rewrite Nat.eqIsEqual m n in natEqualBelow m n h

theorem natEqualBelow: (m: Nat) -> (n: Nat) -> m < n -> Nat.equal m n = False
  | m,      Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Zero,   Succ n, h => rfl
  | Succ m, Succ n, h => natEqualBelow m n h

theorem natEqAbove (m: Nat) (n: Nat) (h: n < m): (m == n) = False :=
  rewrite Nat.eqIsEqual m n in Nat.equalOfLess n m h

theorem ltSucc (m: Nat) (n: Nat) (h: m < n): m < n + 1 :=
  rewrite Nat.addOne n in Nat.leTrans (Succ m) n (Succ n) h (Nat.leSucc n)

-- Past the right edge there is no splitter.
theorem splitterPast (row: Vec Bool w) (c: Nat) (h: w <= c): splitterAt row c = False :=
  List.getOrPast False c (Vec.toList row) (rewrite Vec.lengthToList row in h)

-- Timelines and where the particle can fall ----------------------------------

-- A timeline reaches the splitter in row x, column d.
def hitIn (x: Nat) (d: Nat) (t: List Hit): Bool := t.any (hit => hit.row == x && hit.column == d)

-- A particle falling into column c of the first of `ls` can fall into
-- column d of row k (the first row is row 0).
def reach: List (Vec Bool w) -> Nat -> Nat -> Nat -> Bool
  | ls,            c, Zero,   d => c == d
  | Nil,           c, Succ k, d => False
  | Cons row rest, c, Succ k, d =>
    if splitterAt row c then
      (match c with
         | Zero   => False
         | Succ b => reach rest b k d)
        || reach rest (c + 1) k d
    else reach rest c k d

-- There is a splitter in row k, column d of `ls`.
def splitterIn: List (Vec Bool w) -> Nat -> Nat -> Bool
  | Nil,           k,      d => False
  | Cons row rest, Zero,   d => splitterAt row d
  | Cons row rest, Succ k, d => splitterIn rest k d

-- Putting a splitter that isn't the one looked for in front of every
-- timeline changes nothing.
theorem anyConsMiss (x: Nat) (d: Nat) (h: Hit) (miss: (h.row == x && h.column == d) = False):
    (ts: List (List Hit)) -> List.any (hitIn x d) (List.map (Cons h) ts) = List.any (hitIn x d) ts
  | Nil       => rfl
  | Cons t ts => rewrite miss, anyConsMiss x d h miss ts

-- There is always at least one timeline.
theorem timelinesSome: (r: Nat) -> (c: Nat) -> (ls: List (Vec Bool w)) -> 0 < List.length (timelinesFrom r c ls)
  | r, c, Nil           => rfl
  | r, c, Cons row rest =>
    match e: splitterAt row c with
      | True  =>
        rewrite List.lengthAppend _ _, List.lengthMap _ _ in
          Nat.leTrans 1 (List.length (timelinesFrom (r + 1) (c + 1) rest)) _
            (timelinesSome (r + 1) (c + 1) rest) (Nat.leAddLeft _ _)
      | False => timelinesSome (r + 1) c rest

-- ... so putting the splitter looked for in front of them finds it.
theorem anyConsHit (x: Nat) (d: Nat) (h: Hit) (hit: (h.row == x && h.column == d) = True):
    (ts: List (List Hit)) -> 0 < List.length ts -> List.any (hitIn x d) (List.map (Cons h) ts) = True
  | Nil,       some => Void.exfalso (Bool.falseNotTrue some)
  | Cons t ts, some => rewrite hit

-- No timeline from row r reaches a splitter above it.
theorem noHitsAbove (x: Nat) (d: Nat): (r: Nat) -> (c: Nat) -> (ls: List (Vec Bool w)) -> x < r -> List.any (hitIn x d) (timelinesFrom r c ls) = False
  | r, c, Nil,           h => rfl
  | r, c, Cons row rest, h =>
    let miss: (turn: Turn) -> (({ row = r, column = c, turn }: Hit).row == x && ({ row = r, column = c, turn }: Hit).column == d) = False :=
      turn => rewrite natEqAbove r x h
    match e: splitterAt row c with
      | True  =>
        rewrite List.anyAppend (hitIn x d) _ _, anyConsMiss x d { row = r, column = c, turn = Right } (miss Right) _,
          noHitsAbove x d (r + 1) (c + 1) rest (ltSucc x r h) in
          match c with
            | Zero   => rewrite miss Left
            | Succ b => rewrite anyConsMiss x d { row = r, column = Succ b, turn = Left } (miss Left) _, noHitsAbove x d (r + 1) b rest (ltSucc x r h)
      | False => noHitsAbove x d (r + 1) c rest (ltSucc x r h)

theorem ltSelfSucc (r: Nat): r < r + 1 := rewrite Nat.addOne r in Nat.leRefl (Succ r)

theorem shift (k: Nat) (r: Nat): k + (r + 1) = Succ (k + r) := rewrite Nat.addOne r in Nat.addSucc k r

-- A timeline reaches the splitter in row k (counted from r), column d,
-- exactly when there is a splitter there and the particle can fall into it.
theorem hitsAt: (ls: List (Vec Bool w)) -> (r: Nat) -> (c: Nat) -> (k: Nat) -> (d: Nat) ->
    List.any (hitIn (k + r) d) (timelinesFrom r c ls) = (splitterIn ls k d && reach ls c k d)
  | Nil,           r, c, k,      d => rfl
  | Cons row rest, r, c, Zero,   d =>
    match e: splitterAt row c with
      | True  =>
        match f: c == d with
          | True  =>
            rewrite <- DecEq.sound c d f, e, List.anyAppend (hitIn r c) _ _,
              anyConsHit r c ({ row = r, column = c, turn = Right }: Hit) (rewrite natEqSelf r, natEqSelf c)
                (timelinesFrom (r + 1) (c + 1) rest) (timelinesSome (r + 1) (c + 1) rest)
              in Bool.orTrue _
          | False =>
            rewrite Bool.andFalse (splitterAt row d), List.anyAppend (hitIn r d) _ _,
              anyConsMiss r d ({ row = r, column = c, turn = Right }: Hit) (rewrite natEqSelf r, f) _,
              noHitsAbove r d (r + 1) (c + 1) rest (ltSelfSucc r) in
              match c with
                | Zero   => rewrite natEqSelf r, f
                | Succ b => rewrite anyConsMiss r d ({ row = r, column = Succ b, turn = Left }: Hit) (rewrite natEqSelf r, f) _,
                              noHitsAbove r d (r + 1) b rest (ltSelfSucc r)
      | False =>
        rewrite noHitsAbove r d (r + 1) c rest (ltSelfSucc r) in
          match f: c == d with
            | True  => rewrite <- DecEq.sound c d f, e
            | False => rewrite Bool.andFalse (splitterAt row d)
  | Cons row rest, r, c, Succ k, d =>
    let ih: (c2: Nat) -> List.any (hitIn (Succ (k + r)) d) (timelinesFrom (r + 1) c2 rest) = (splitterIn rest k d && reach rest c2 k d) :=
      c2 => rewrite <- shift k r in hitsAt rest (r + 1) c2 k d
    let above: (r == Succ (k + r)) = False := natEqBelow r (Succ (k + r)) (Nat.leAddLeft k r)
    match e: splitterAt row c with
      | True  =>
        rewrite List.anyAppend (hitIn (Succ (k + r)) d) _ _,
          anyConsMiss (Succ (k + r)) d ({ row = r, column = c, turn = Right }: Hit) (rewrite above) _, ih (c + 1) in
          match c with
            | Zero   => rewrite above
            | Succ b => rewrite anyConsMiss (Succ (k + r)) d ({ row = r, column = Succ b, turn = Left }: Hit) (rewrite above) _, ih b in andOr _ _ _
      | False => ih c

-- Past the right edge there are no splitters: a particle there stays there.
theorem reachPast (w: Nat): (ls: List (Vec Bool w)) -> (c: Nat) -> (k: Nat) -> (d: Nat) -> w <= c -> d < w -> reach ls c k d = False
  | ls,            c, Zero,   d, hc, hd => natEqAbove c d (Nat.leTrans (Succ d) w c hd hc)
  | Nil,           c, Succ k, d, hc, hd => rfl
  | Cons row rest, c, Succ k, d, hc, hd =>
    rewrite splitterPast row c hc in reachPast w rest c k d hc hd

-- The program's side ----------------------------------------------------------

-- Or, from one of its sides.
theorem orFirst (x: Bool) (y: Bool) (z: Bool) (h: x = True): (x || (y || z)) = True := rewrite h
theorem orSecond (x: Bool) (y: Bool) (z: Bool) (h: y = True): (x || (y || z)) = True := rewrite h, Bool.orTrue x
theorem orThird (x: Bool) (y: Bool) (z: Bool) (h: z = True): (x || (y || z)) = True := rewrite h, Bool.orTrue y, Bool.orTrue x

-- A flag that is set is inside the row.
theorem setInside: (xs: List Bool) -> (i: Nat) -> List.getOr False i xs = True -> i < List.length xs
  | Nil,       i,      h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Zero,   h => rfl
  | Cons x xs, Succ i, h => setInside xs i h

-- What comes into column c of `fall`'s result from the left.
def fromLeft (fl: Bool) (ss: List Bool) (bs: List Bool): Nat -> Bool
  | Zero   => fl
  | Succ b => List.getOr False b ss && List.getOr False b bs

-- `fall` column by column: a beam passes a column without a splitter, and
-- the splitters beside it send theirs.
theorem fallAt: (fl: Bool) -> (ss: List Bool) -> (bs: List Bool) -> List.length ss = List.length bs -> (c: Nat) -> c < List.length bs ->
    List.getOr False c (fall fl ss bs)
      = ((List.getOr False c bs && Bool.not (List.getOr False c ss)) || (fromLeft fl ss bs c || (List.getOr False (Succ c) ss && List.getOr False (Succ c) bs)))
  | fl, Nil,       Nil,       e, c,      h => Void.exfalso (Bool.falseNotTrue h)
  | fl, Nil,       Cons b bs, e, c,      h => Void.exfalso (Nat.zeroNotSucc (List.length bs) e)
  | fl, Cons s ss, Nil,       e, c,      h => Void.exfalso (Nat.succNotZero (List.length ss) e)
  | fl, Cons s ss, Cons b bs, e, Zero,   h => rewrite List.headOrGetOr False ss, List.headOrGetOr False bs
  | fl, Cons s ss, Cons b bs, e, Succ c, h =>
    match c with
      | Zero    => fallAt (s && b) ss bs (Nat.succInjective (List.length ss) (List.length bs) e) Zero h
      | Succ c2 => fallAt (s && b) ss bs (Nat.succInjective (List.length ss) (List.length bs) e) (Succ c2) h

theorem fallLength: (fl: Bool) -> (ss: List Bool) -> (bs: List Bool) -> List.length ss = List.length bs -> List.length (fall fl ss bs) = List.length bs
  | fl, Nil,       Nil,       e => rfl
  | fl, Nil,       Cons b bs, e => Void.exfalso (Nat.zeroNotSucc (List.length bs) e)
  | fl, Cons s ss, Nil,       e => Void.exfalso (Nat.succNotZero (List.length ss) e)
  | fl, Cons s ss, Cons b bs, e => Eq.cong Succ (fallLength (s && b) ss bs (Nat.succInjective (List.length ss) (List.length bs) e))

-- The splitters a row's beams reach, column by column.
theorem zipSum: (ss: List Bool) -> (bs: List Bool) -> List.length ss = List.length bs ->
    List.sumBy (x => Bool.toNat x) (List.zipWith (s b => s && b) ss bs)
      = List.sumBy (d => Bool.toNat (List.getOr False d ss && List.getOr False d bs)) (List.range (List.length bs))
  | Nil,       Nil,       e => rfl
  | Nil,       Cons b bs, e => Void.exfalso (Nat.zeroNotSucc (List.length bs) e)
  | Cons s ss, Nil,       e => Void.exfalso (Nat.succNotZero (List.length ss) e)
  | Cons s ss, Cons b bs, e =>
    calc List.sumBy (x => Bool.toNat x) (Cons (s && b) (List.zipWith (s b => s && b) ss bs))
      _ = Bool.toNat (s && b) + List.sumBy (x => Bool.toNat x) (List.zipWith (s b => s && b) ss bs)
          := List.sumByCons (x => Bool.toNat x) (s && b) (List.zipWith (s b => s && b) ss bs)
      _ = Bool.toNat (s && b) + List.sumBy (d => Bool.toNat (List.getOr False d ss && List.getOr False d bs)) (List.range (List.length bs))
          := rewrite zipSum ss bs (Nat.succInjective (List.length ss) (List.length bs) e)
      _ = List.sumBy (d => Bool.toNat (List.getOr False d (Cons s ss) && List.getOr False d (Cons b bs))) (List.rangeFrom (Succ (List.length bs)) 0)
          := Eq.sym (Eq.trans (List.sumByCons (d => Bool.toNat (List.getOr False d (Cons s ss) && List.getOr False d (Cons b bs))) 0 (List.rangeFrom (List.length bs) 1))
               (Eq.cong (t => Bool.toNat (s && b) + t)
                  (List.sumByRangeShift (d => Bool.toNat (List.getOr False d (Cons s ss) && List.getOr False d (Cons b bs))) (List.length bs) 0)))

theorem splitsInSum (ss: List Bool) (bs: List Bool) (e: List.length ss = List.length bs):
    splitsIn ss bs = List.sumBy (d => Bool.toNat (List.getOr False d ss && List.getOr False d bs)) (List.range (List.length bs)) :=
  Eq.trans (List.countSumBy (x => x) (List.zipWith (s b => s && b) ss bs)) (zipSum ss bs e)

-- The particle can fall into column d of row k from a column with a beam.
def beamReach (w: Nat) (beams: List Bool) (ls: List (Vec Bool w)) (k: Nat) (d: Nat): Bool :=
  List.any (c => List.getOr False c beams && reach ls c k d) (List.range w)

-- In the first row, that is the beams themselves.
theorem beamReachZero (w: Nat) (beams: List Bool) (ls: List (Vec Bool w)) (d: Nat) (hd: d < w): beamReach w beams ls 0 d = List.getOr False d beams :=
  Bool.eqOf (beamReach w beams ls 0 d) (List.getOr False d beams)
    (h => List.anyRangeElim (c => List.getOr False c beams && reach ls c 0 d) (List.getOr False d beams = True) w 0 h
       (c lo hi hc => rewrite <- DecEq.sound c d (Bool.andRight (List.getOr False c beams) (c == d) hc) in Bool.andLeft (List.getOr False c beams) (c == d) hc))
    (h => List.anyRangeIntro (c => List.getOr False c beams && reach ls c 0 d) w 0 d (Nat.zeroLe d) hd
       (Bool.andIntro (List.getOr False d beams) (d == d) h (natEqSelf d)))

-- One row of `fall` carries the beams down: the particle can fall into
-- column d of row k below the row from a column with a beam after it, when
-- it can fall there from one with a beam before it.
theorem fallKeeps (w: Nat) (row: Vec Bool w) (rest: List (Vec Bool w))
    (beams: List Bool) (hb: List.length beams = w) (k: Nat) (d: Nat) (hd: d < w):
    beamReach w (fall False (Vec.toList row) beams) rest k d = beamReach w beams (Cons row rest) (Succ k) d :=
  let flags := Vec.toList row
  let fallen := fall False flags beams
  let hf: List.length flags = List.length beams := rewrite Vec.lengthToList row, hb
  let at: (c: Nat) -> c < w -> List.getOr False c fallen
      = ((List.getOr False c beams && Bool.not (List.getOr False c flags)) || (fromLeft False flags beams c || (List.getOr False (Succ c) flags && List.getOr False (Succ c) beams))) :=
    c hc => fallAt False flags beams hf c (rewrite hb in hc)
  let after: Nat -> Bool := c => List.getOr False c fallen && reach rest c k d
  let before: Nat -> Bool := c => List.getOr False c beams && reach (Cons row rest) c (Succ k) d
  Bool.eqOf (beamReach w fallen rest k d) (beamReach w beams (Cons row rest) (Succ k) d)
    (h => List.anyRangeElim after (beamReach w beams (Cons row rest) (Succ k) d = True) w 0 h
       (c lo hi hc =>
         let hr := Bool.andRight (List.getOr False c fallen) (reach rest c k d) hc
         let into := Eq.trans (Eq.sym (at c hi)) (Bool.andLeft (List.getOr False c fallen) (reach rest c k d) hc)
         orCases (beamReach w beams (Cons row rest) (Succ k) d = True) _ _ into
           (h1 =>
             let hB := Bool.andLeft (List.getOr False c beams) (Bool.not (List.getOr False c flags)) h1
             let hF: splitterAt row c = False := notTrue (List.getOr False c flags) (Bool.andRight (List.getOr False c beams) (Bool.not (List.getOr False c flags)) h1)
             List.anyRangeIntro before w 0 c lo hi (Bool.andIntro (List.getOr False c beams) (reach (Cons row rest) c (Succ k) d) hB (rewrite hF in hr)))
           (h2 => orCases (beamReach w beams (Cons row rest) (Succ k) d = True) _ _ h2
             (h3 =>
               match c with
                 | Zero   => Void.exfalso (Bool.falseNotTrue h3)
                 | Succ b =>
                   let hF: splitterAt row b = True := Bool.andLeft (List.getOr False b flags) (List.getOr False b beams) h3
                   let hB := Bool.andRight (List.getOr False b flags) (List.getOr False b beams) h3
                   List.anyRangeIntro before w 0 b (Nat.zeroLe b) (Nat.lessTrans b (Succ b) w (Nat.leRefl (Succ b)) hi)
                     (Bool.andIntro (List.getOr False b beams) (reach (Cons row rest) b (Succ k) d) hB
                        (rewrite hF, Nat.addOne b, hr in Bool.orTrue _)))
             (h4 =>
               let hF: splitterAt row (Succ c) = True := Bool.andLeft (List.getOr False (Succ c) flags) (List.getOr False (Succ c) beams) h4
               let hB := Bool.andRight (List.getOr False (Succ c) flags) (List.getOr False (Succ c) beams) h4
               let inside: Succ c < w := rewrite <- hb in setInside beams (Succ c) hB
               List.anyRangeIntro before w 0 (Succ c) (Nat.zeroLe (Succ c)) inside
                 (Bool.andIntro (List.getOr False (Succ c) beams) (reach (Cons row rest) (Succ c) (Succ k) d) hB (rewrite hF, hr))))))
    (h => List.anyRangeElim before (beamReach w fallen rest k d = True) w 0 h
       (c lo hi hc =>
         let hB := Bool.andLeft (List.getOr False c beams) (reach (Cons row rest) c (Succ k) d) hc
         let hr := Bool.andRight (List.getOr False c beams) (reach (Cons row rest) c (Succ k) d) hc
         match e: splitterAt row c with
           | True  =>
             orCases (beamReach w fallen rest k d = True) _ (reach rest (c + 1) k d)
               hr
               (hl =>
                 match c with
                   | Zero   => Void.exfalso (Bool.falseNotTrue hl)
                   | Succ b =>
                     let hb2: b < w := Nat.lessTrans b (Succ b) w (Nat.leRefl (Succ b)) hi
                     List.anyRangeIntro after w 0 b (Nat.zeroLe b) hb2
                       (Bool.andIntro (List.getOr False b fallen) (reach rest b k d)
                          (rewrite at b hb2 in orThird _ _ _ (Bool.andIntro (List.getOr False (Succ b) flags) (List.getOr False (Succ b) beams) e hB))
                          hl))
               (hrr =>
                 match g: Nat.leq (Succ (Succ c)) w with
                   | True  =>
                     List.anyRangeIntro after w 0 (Succ c) (Nat.zeroLe (Succ c)) g
                       (Bool.andIntro (List.getOr False (Succ c) fallen) (reach rest (Succ c) k d)
                          (rewrite at (Succ c) g in orSecond _ _ _ (Bool.andIntro (List.getOr False c flags) (List.getOr False c beams) e hB))
                          (rewrite <- Nat.addOne c in hrr))
                   | False =>
                     Void.exfalso (Bool.falseNotTrue
                       (Eq.trans (Eq.sym (reachPast w rest (Succ c) k d (Nat.leqFalse (Succ (Succ c)) w g) hd)) (rewrite <- Nat.addOne c in hrr))))
           | False =>
             List.anyRangeIntro after w 0 c lo hi
               (Bool.andIntro (List.getOr False c fallen) (reach rest c k d)
                  (rewrite at c hi in orFirst _ _ _ (Bool.andIntro (List.getOr False c beams) (Bool.not (List.getOr False c flags)) hB (rewrite e)))
                  hr)))

-- The splitters the beams reach in row k, and all of them below.
def splitsAt (w: Nat) (beams: List Bool) (ls: List (Vec Bool w)) (k: Nat): Nat :=
  List.sumBy (d => Bool.toNat (splitterIn ls k d && beamReach w beams ls k d)) (List.range w)

theorem splitsBelowSum (w: Nat): (ls: List (Vec Bool w)) -> (beams: List Bool) -> List.length beams = w ->
    splitsBelow beams (List.map Vec.toList ls) = List.sumBy (k => splitsAt w beams ls k) (List.range (List.length ls))
  | Nil,         beams, hb => rfl
  | Cons l rest, beams, hb =>
    let flags := Vec.toList l
    let hf: List.length flags = List.length beams := rewrite Vec.lengthToList l, hb
    let fallen := fall False flags beams
    calc splitsIn flags beams + splitsBelow fallen (List.map Vec.toList rest)
      _ = List.sumBy (d => Bool.toNat (List.getOr False d flags && List.getOr False d beams)) (List.range w)
            + List.sumBy (k => splitsAt w fallen rest k) (List.range (List.length rest))
          := rewrite splitsInSum flags beams hf, hb, splitsBelowSum w rest fallen (rewrite fallLength False flags beams hf, hb)
      _ = splitsAt w beams (Cons l rest) 0 + List.sumBy (k => splitsAt w beams (Cons l rest) (Succ k)) (List.range (List.length rest))
          := rewrite
               List.sumRangeCongr (d => Bool.toNat (List.getOr False d flags && List.getOr False d beams))
                 (d => Bool.toNat (splitterAt l d && beamReach w beams (Cons l rest) 0 d)) w 0
                 (d lo hd => rewrite beamReachZero w beams (Cons l rest) d hd),
               List.sumByCongr (k => splitsAt w fallen rest k) (k => splitsAt w beams (Cons l rest) (Succ k))
                 (k => List.sumRangeCongr (d => Bool.toNat (splitterIn rest k d && beamReach w fallen rest k d))
                         (d => Bool.toNat (splitterIn rest k d && beamReach w beams (Cons l rest) (Succ k) d)) w 0
                         (d lo hd => rewrite fallKeeps w l rest beams hb k d hd))
                 (List.range (List.length rest))
      _ = List.sumBy (k => splitsAt w beams (Cons l rest) k) (List.range (Succ (List.length rest)))
          := Eq.sym (Eq.trans (List.sumByCons (k => splitsAt w beams (Cons l rest) k) 0 (List.rangeFrom (List.length rest) 1))
               (Eq.cong (t => splitsAt w beams (Cons l rest) 0 + t) (List.sumByRangeShift (k => splitsAt w beams (Cons l rest) k) (List.length rest) 0)))

-- At the start, the only beam is in S's column.
theorem beamStart (w: Nat) (st: Nat) (hs: st < w) (ls: List (Vec Bool w)) (k: Nat) (d: Nat):
    beamReach w (List.map (x => x == st) (List.range w)) ls k d = reach ls st k d :=
  let start := List.map (x => x == st) (List.range w)
  let at: (c: Nat) -> c < w -> List.getOr False c start = (c == st) :=
    c hc => rewrite List.getOrMapRange (x => x == st) False w 0 c hc, Nat.addZero c
  Bool.eqOf (beamReach w start ls k d) (reach ls st k d)
    (h => List.anyRangeElim (c => List.getOr False c start && reach ls c k d) (reach ls st k d = True) w 0 h
       (c lo hi hc =>
         let same := DecEq.sound c st (Eq.trans (Eq.sym (at c hi)) (Bool.andLeft (List.getOr False c start) (reach ls c k d) hc))
         rewrite <- same in Bool.andRight (List.getOr False c start) (reach ls c k d) hc))
    (h => List.anyRangeIntro (c => List.getOr False c start && reach ls c k d) w 0 st (Nat.zeroLe st) hs
       (Bool.andIntro (List.getOr False st start) (reach ls st k d) (rewrite at st hs in natEqSelf st) h))

-- The splitters some timeline reaches in row k: those the beams reach.
theorem splitsAtReached (manifold: Manifold) (k: Nat):
    splitsAt manifold.width (List.map (x => x == manifold.start.toNat) (List.range manifold.width)) manifold.rows k
      = List.count (d => reached (timelines manifold) k d) (List.range manifold.width) :=
  let w := manifold.width
  let st := manifold.start.toNat
  let start := List.map (x => x == st) (List.range w)
  Eq.trans
    (List.sumByCongr (d => Bool.toNat (splitterIn manifold.rows k d && beamReach w start manifold.rows k d))
       (d => Bool.toNat (reached (timelines manifold) k d))
       (d => rewrite beamStart w st (Fin.toNatLt manifold.start) manifold.rows k d in
          Eq.cong Bool.toNat (Eq.sym (Eq.trans (Eq.cong (x => List.any (hitIn x d) (timelines manifold)) (Eq.sym (Nat.addZero k)))
            (hitsAt manifold.rows 0 st k d))))
       (List.range w))
    (Eq.sym (List.countSumBy (d => reached (timelines manifold) k d) (List.range w)))

-- Part 1 is right: for every manifold, the printed answer is the number of
-- splitters some timeline of the particle from S reaches.
theorem part1Correct (manifold: Manifold): solvePart1 manifold = part1Spec manifold :=
  let start := List.map (x => x == manifold.start.toNat) (List.range manifold.width)
  calc splitsBelow start (List.map Vec.toList manifold.rows)
    _ = List.sumBy (k => splitsAt manifold.width start manifold.rows k) (List.range (List.length manifold.rows))
        := splitsBelowSum manifold.width manifold.rows start
             (rewrite List.lengthMap (x => x == manifold.start.toNat) (List.range manifold.width) in List.lengthRangeFrom manifold.width 0)
    _ = List.sumBy (k => List.count (d => reached (timelines manifold) k d) (List.range manifold.width)) (List.range (List.length manifold.rows))
        := List.sumByCongr _ _
             (k => splitsAtReached manifold k) (List.range (List.length manifold.rows))
