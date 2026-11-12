--| Day 7, part 1, proved for every manifold (`part1Correct`, at the bottom):
--| the program's count is the number of splitters some timeline of
--| Spec/Spec.sw reaches.
--
-- The argument:
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

namespace Aoc.Year2025.Day07.Proofs
import Aoc.Year2025.Day07 (..)
import Aoc.Year2025.Day07.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, Fin, List, Nat, Option, Vec, Void)

-- Bool and number facts ------------------------------------------------------

theorem andOr (a: Bool) [x: Bool] [y: Bool]: ((a ∧ x) ∨ (a ∧ y)) = (a ∧ (x ∨ y)) :=
  match a with
    | True => rfl
    | False => rfl

theorem natEqSelf (n: Nat): (n == n) = True := (DecEq.decide n n).complete rfl

theorem natEqBelow (m: Nat) (n: Nat) (h: m < n): (m == n) = False := Decidable.toBoolOfNot (DecEq.decide m n) (e => omega)

theorem natEqAbove (m: Nat) (n: Nat) (h: n < m): (m == n) = False := Decidable.toBoolOfNot (DecEq.decide m n) (e => omega)

theorem ltSucc (m: Nat) (n: Nat) (h: m < n): m < n + 1 := omega

--| Past the right edge there is no splitter.
theorem splitterPast (row: Vec Bool w) (c: Nat) (h: w ≤ c): splitterAt row c = False :=
  Vec.getOrPast row c False h

-- Timelines and where the particle can fall ----------------------------------

--| A timeline reaches the splitter in row x, column d.
def hitIn (x: Nat) (d: Nat) (t: List Hit): Bool := t.any (hit => hit.row == x ∧ hit.column == d)

--| A particle falling into column c of the first of `ls` can fall into
--| column d of row k (the first row is row 0).
def reach: List (Vec Bool w) → Nat → Nat → Nat → Bool
  | ls, c, Zero, d => c == d
  | [], c, Succ k, d => False
  | [row, ..rest], c, Succ k, d =>
    if splitterAt row c then
      (match c with
          | Zero => False
          | Succ b => reach rest b k d)
        ∨ reach rest (c + 1) k d
    else reach rest c k d

--| There is a splitter in row k, column d of `ls`.
def splitterIn: List (Vec Bool w) → Nat → Nat → Bool
  | [], k, d => False
  | [row, ..rest], Zero, d => splitterAt row d
  | [row, ..rest], Succ k, d => splitterIn rest k d

--| Putting a splitter that isn't the one looked for in front of every
--| timeline changes nothing.
theorem anyConsMiss (x: Nat) (d: Nat) (h: Hit) (miss: (h.row == x ∧ h.column == d) = False)
    (ts: List (List Hit)): (ts.map (Cons h)).any (hitIn x d) = ts.any (hitIn x d) :=
  match ts with
    | [] => rfl
    | [t, ..ts] => rewrite miss, anyConsMiss x d h miss ts

--| There is always at least one timeline.
theorem timelinesSome (r c: Nat) (ls: List (Vec Bool w)): 0 < List.length (timelinesFrom r c ls) :=
  match ls with
    | [] => rfl
    | [row, ..rest] =>
      match e: splitterAt row c with
        | True =>
          rewrite List.lengthAppend _ _, List.lengthMap _ _ in
            omega [timelinesSome (r + 1) (c + 1) rest]
        | False => timelinesSome (r + 1) c rest

--| ... so putting the splitter looked for in front of them finds it.
theorem anyConsHit (x: Nat) (d: Nat) (h: Hit) (hit: (h.row == x ∧ h.column == d) = True)
    (ts: List (List Hit)) (some: 0 < ts.length): (ts.map (Cons h)).any (hitIn x d) = True :=
  match ts with
    | [t, ..ts] => rewrite hit

--| No timeline from row r reaches a splitter above it.
theorem noHitsAbove (x: Nat) (d: Nat) (r c: Nat) (ls: List (Vec Bool w)) (h: x < r): List.any (timelinesFrom r c ls) (hitIn x d) = False :=
  match ls with
    | [] => rfl
    | [row, ..rest] =>
      let miss: ∀ (turn: Turn) => (({ row = r, column = c, turn }: Hit).row == x ∧ ({ row = r, column = c, turn }: Hit).column == d) = False :=
        turn => rewrite natEqAbove r x h
      match e: splitterAt row c with
        | True =>
          rewrite List.anyAppend _ _ (hitIn x d), anyConsMiss x d { row = r, column = c, turn = Right } (miss Right) _,
            noHitsAbove x d (r + 1) (c + 1) rest (ltSucc x r h) in
            match c with
              | Zero => rewrite miss Left
              | Succ b => rewrite anyConsMiss x d { row = r, column = Succ b, turn = Left } (miss Left) _, noHitsAbove x d (r + 1) b rest (ltSucc x r h)
        | False => noHitsAbove x d (r + 1) c rest (ltSucc x r h)

theorem ltSelfSucc (r: Nat): r < r + 1 := omega

theorem shift (k: Nat) (r: Nat): k + (r + 1) = Succ (k + r) := omega

--| A timeline reaches the splitter in row k (counted from r), column d,
--| exactly when there is a splitter there and the particle can fall into it.
theorem hitsAt (ls: List (Vec Bool w)) (r c k d: Nat):
    List.any (timelinesFrom r c ls) (hitIn (k + r) d) = (splitterIn ls k d ∧ reach ls c k d) :=
  match ls, k with
    | [], k => rfl
    | [row, ..rest], Zero =>
      match e: splitterAt row c with
        | True =>
          match f: c == d with
            | True =>
              rewrite <- DecEq.sound f, e, List.anyAppend _ _ (hitIn r c),
                anyConsHit r c ({ row = r, column = c, turn = Right }: Hit) (rewrite natEqSelf r, natEqSelf c)
                  (timelinesFrom (r + 1) (c + 1) rest) (timelinesSome (r + 1) (c + 1) rest)
                in Bool.orTrue _
            | False =>
              rewrite Bool.andFalse (splitterAt row d), List.anyAppend _ _ (hitIn r d),
                anyConsMiss r d ({ row = r, column = c, turn = Right }: Hit) (rewrite natEqSelf r, f) _,
                noHitsAbove r d (r + 1) (c + 1) rest (ltSelfSucc r) in
                match c with
                  | Zero => rewrite natEqSelf r, f
                  | Succ b => rewrite anyConsMiss r d ({ row = r, column = Succ b, turn = Left }: Hit) (rewrite natEqSelf r, f) _,
                    noHitsAbove r d (r + 1) b rest (ltSelfSucc r)
        | False =>
          rewrite noHitsAbove r d (r + 1) c rest (ltSelfSucc r) in
            match f: c == d with
              | True => rewrite <- DecEq.sound f, e
              | False => rewrite Bool.andFalse (splitterAt row d)
    | [row, ..rest], Succ k =>
      let ih: ∀ (c2: Nat) => List.any (timelinesFrom (r + 1) c2 rest) (hitIn (Succ (k + r)) d) = (splitterIn rest k d ∧ reach rest c2 k d) :=
        c2 => rewrite <- shift k r in hitsAt rest (r + 1) c2 k d
      let above: (r == Succ (k + r)) = False := natEqBelow r (Succ (k + r)) omega
      match e: splitterAt row c with
        | True =>
          rewrite List.anyAppend _ _ (hitIn (Succ (k + r)) d),
            anyConsMiss (Succ (k + r)) d ({ row = r, column = c, turn = Right }: Hit) (rewrite above) _, ih (c + 1) in
            match c with
              | Zero => rewrite above
              | Succ b => rewrite anyConsMiss (Succ (k + r)) d ({ row = r, column = Succ b, turn = Left }: Hit) (rewrite above) _, ih b in andOr _
        | False => ih c

--| Past the right edge there are no splitters: a particle there stays there.
theorem reachPast (w: Nat) (ls: List (Vec Bool w)) (c k d: Nat) (hc: w ≤ c) (hd: d < w): reach ls c k d = False :=
  match ls, k with
    | ls, Zero => natEqAbove c d omega
    | [], Succ k => rfl
    | [row, ..rest], Succ k =>
      rewrite splitterPast row c hc in reachPast w rest c k d hc hd

-- The program's side ----------------------------------------------------------

--| A flag that is set is inside the row.
theorem setInside (v: Vec Bool w) (i: Nat) (h: v.getOr i False = True): i < w :=
  match g: Nat.leq (Succ i) w with
    | True => rfl
    | False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (Vec.getOrPast v i False omega)) h))

--| What comes into column c of `fall`'s result from the left.
def fromLeft (row: Vec Bool w) (beams: Vec Bool w): Nat → Bool
  | Zero => False
  | Succ b => splitterAt row b ∧ beams.getOr b False

--| `fall` column by column: a beam passes a column without a splitter, and
--| the splitters beside it send theirs.
theorem fallAt (row: Vec Bool w) (beams: Vec Bool w) (c: Nat) (h: c < w):
    (fall row beams).getOr c False
      = ((beams.getOr c False ∧ ¬(splitterAt row c))
        ∨ (fromLeft row beams c ∨ (splitterAt row (Succ c) ∧ beams.getOr (Succ c) False))) :=
  let hit := Vec.zipWith row beams (s b => s ∧ b)
  rewrite Vec.getOrZipWith3 (pass left right => pass ∨ (left ∨ right)) False False False False rfl
        (Vec.zipWith row beams (s b => b ∧ not s)) (hit.shiftRight False) (hit.shiftLeft False) c,
      Vec.getOrZipWith (s b => b ∧ not s) False False False rfl row beams c,
      Vec.getOrShiftRight hit c False False h, Vec.getOrShiftLeft hit False c,
      Vec.getOrZipWith (s b => s ∧ b) False False False rfl row beams (Succ c) in
    match c with
      | Zero => rfl
      | Succ b => rewrite Vec.getOrZipWith (s b => s ∧ b) False False False rfl row beams b

--| The splitters a row's beams reach, column by column.
theorem splitsInSum (row: Vec Bool w) (beams: Vec Bool w):
    splitsIn row beams = List.sumBy (List.range 0 w) (d => Bool.toNat (splitterAt row d ∧ beams.getOr d False)) :=
  let hit := Vec.zipWith row beams (s b => s ∧ b)
  rewrite Vec.countSumBy hit (x => x), Vec.sumByGetOr hit False (x => Bool.toNat x),
    Vec.getOrZipWith (s b => s ∧ b) False False False rfl row beams _

--| The particle can fall into column d of row k from a column with a beam.
def beamReach (beams: Vec Bool w) (ls: List (Vec Bool w)) (k: Nat) (d: Nat): Bool :=
  List.any (List.range 0 w) (c => beams.getOr c False ∧ reach ls c k d)

--| In the first row, that is the beams themselves.
theorem beamReachZero (beams: Vec Bool w) (ls: List (Vec Bool w)) (d: Nat) (hd: d < w): beamReach beams ls 0 d = beams.getOr d False :=
  Bool.eqOf (beamReach beams ls 0 d) (beams.getOr d False)
    (h => List.anyRangeElim (c => beams.getOr c False ∧ reach ls c 0 d) (beams.getOr d False = True) w 0 h
      (c lo hi hc => rewrite <- DecEq.sound (Bool.andRight hc) in Bool.andLeft hc))
    (h => List.anyRangeIntro (c => beams.getOr c False ∧ reach ls c 0 d) w 0 d omega hd
      (Bool.andIntro h (natEqSelf d)))

-- One row of `fall` carries the beams down (`fallKeeps`). A beam comes out
-- of a row in three ways, and each is a way the particle goes on falling:
-- straight down, or from a splitter on its left or on its right. Each lemma
-- shows both sides of `fallKeeps` true in its case.

--| Straight down: a beam in column c without a splitter passes it.
theorem fallStraight (row: Vec Bool w) (rest: List (Vec Bool w)) (v: Vec Bool w) (k: Nat) (d: Nat) (c: Nat)
    (beam: v.getOr c False = True) (empty: splitterAt row c = False) (on: reach rest c k d = True):
    beamReach (fall row v) rest k d = True ∧ beamReach v [row, ..rest] (Succ k) d = True :=
  let inside := setInside v c beam
  Both
    (List.anyRangeIntro (c => (fall row v).getOr c False ∧ reach rest c k d) w 0 c omega inside
      (Bool.andIntro (rewrite fallAt row v c inside in Bool.orLeft (Bool.andIntro beam (rewrite empty))) on))
    (List.anyRangeIntro (c => v.getOr c False ∧ reach [row, ..rest] c (Succ k) d) w 0 c omega inside
      (Bool.andIntro beam (rewrite empty in on)))

--| From the left: a splitter in column b with a beam sends one down column
--| b + 1, where the particle goes right. (That column is inside the row, as
--| the particle can still fall into column d: past the right edge it
--| couldn't.)
theorem fallFromLeft (row: Vec Bool w) (rest: List (Vec Bool w)) (v: Vec Bool w) (k: Nat) (d: Nat) (hd: d < w) (b: Nat)
    (beam: v.getOr b False = True) (splitter: splitterAt row b = True) (on: reach rest (Succ b) k d = True):
    beamReach (fall row v) rest k d = True ∧ beamReach v [row, ..rest] (Succ k) d = True :=
  let inside: Succ b < w :=
    match g: Nat.leq (Succ (Succ b)) w with
      | True => rfl
      | False => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (reachPast w rest (Succ b) k d omega hd)) on))
  Both
    (List.anyRangeIntro (c => (fall row v).getOr c False ∧ reach rest c k d) w 0 (Succ b) omega inside
      (Bool.andIntro (rewrite fallAt row v (Succ b) inside in Bool.orRight (Bool.orLeft (Bool.andIntro splitter beam))) on))
    (List.anyRangeIntro (c => v.getOr c False ∧ reach [row, ..rest] c (Succ k) d) w 0 b omega (setInside v b beam)
      (Bool.andIntro beam (rewrite splitter, Nat.addOne b, on in Bool.orTrue _)))

--| From the right: a splitter in column c + 1 with a beam sends one down
--| column c, where the particle goes left.
theorem fallFromRight (row: Vec Bool w) (rest: List (Vec Bool w)) (v: Vec Bool w) (k: Nat) (d: Nat) (c: Nat)
    (beam: v.getOr (Succ c) False = True) (splitter: splitterAt row (Succ c) = True) (on: reach rest c k d = True):
    beamReach (fall row v) rest k d = True ∧ beamReach v [row, ..rest] (Succ k) d = True :=
  let inside: Succ c < w := setInside v (Succ c) beam
  let left: c < w := omega [inside]
  Both
    (List.anyRangeIntro (c => (fall row v).getOr c False ∧ reach rest c k d) w 0 c omega left
      (Bool.andIntro (rewrite fallAt row v c left in Bool.orRight (Bool.orRight (Bool.andIntro splitter beam))) on))
    (List.anyRangeIntro (c => v.getOr c False ∧ reach [row, ..rest] c (Succ k) d) w 0 (Succ c) omega inside
      (Bool.andIntro beam (rewrite splitter, on)))

--| The particle can fall into column d of row k below the row from a column
--| with a beam after it, when it can fall there from one with a beam before
--| it.
theorem fallKeeps (row: Vec Bool w) (rest: List (Vec Bool w)) (v: Vec Bool w) (k: Nat) (d: Nat) (hd: d < w):
    beamReach (fall row v) rest k d = beamReach v [row, ..rest] (Succ k) d :=
  let after: Nat → Bool := c => (fall row v).getOr c False ∧ reach rest c k d
  let before: Nat → Bool := c => v.getOr c False ∧ reach [row, ..rest] c (Succ k) d
  Bool.eqOf (beamReach (fall row v) rest k d) (beamReach v [row, ..rest] (Succ k) d)
    -- A beam out of the row in column c came straight down, from the left or
    -- from the right.
    (h => List.anyRangeElim after (beamReach v [row, ..rest] (Succ k) d = True) w 0 h
      (c lo hi hc =>
        let on := Bool.andRight hc
        Bool.orElim (Eq.trans (Eq.sym (fallAt row v c hi)) (Bool.andLeft hc))
          (pass => (fallStraight row rest v k d c (Bool.andLeft pass) (Bool.notTrue _ (Bool.andRight pass)) on).right)
          (sides => Bool.orElim sides
            (left =>
              match c with
                | Succ b => (fallFromLeft row rest v k d hd b (Bool.andRight left) (Bool.andLeft left) on).right)
            (right => (fallFromRight row rest v k d c (Bool.andRight right) (Bool.andLeft right) on).right))))
    -- A particle in column c with a beam falls straight down, or at a
    -- splitter goes left or right.
    (h => List.anyRangeElim before (beamReach (fall row v) rest k d = True) w 0 h
      (c lo hi hc =>
        let beam := Bool.andLeft hc
        let on := Bool.andRight hc
        match e: splitterAt row c with
          | False => (fallStraight row rest v k d c beam e on).left
          | True =>
            Bool.orElim on
              (left =>
                match c with
                  | Succ b => (fallFromRight row rest v k d b beam e left).left)
              (right => (fallFromLeft row rest v k d hd c beam e (rewrite <- Nat.addOne c in right)).left)))

--| The splitters the beams reach in row k, and all of them below.
def splitsAt (beams: Vec Bool w) (ls: List (Vec Bool w)) (k: Nat): Nat :=
  List.sumBy (List.range 0 w) (d => Bool.toNat (splitterIn ls k d ∧ beamReach beams ls k d))

theorem splitsBelowSum (w: Nat) (ls: List (Vec Bool w)) (beams: Vec Bool w):
    splitsBelow beams ls = List.sumBy (List.range 0 ls.length) (k => splitsAt beams ls k) :=
  match ls with
    | [] => rfl
    | [l, ..rest] =>
      let fallen := fall l beams
      calc splitsIn l beams + splitsBelow fallen rest
        _ = List.sumBy (List.range 0 w) (d => Bool.toNat (splitterAt l d ∧ beams.getOr d False))
            + List.sumBy (List.range 0 rest.length) (k => splitsAt fallen rest k)
          := rewrite splitsInSum l beams, splitsBelowSum w rest fallen
        _ = splitsAt beams [l, ..rest] 0 + List.sumBy (List.range 0 rest.length) (k => splitsAt beams [l, ..rest] (Succ k))
          := rewrite beamReachZero beams [l, ..rest], fallKeeps l rest beams
        _ = List.sumBy (List.range 0 (Succ rest.length)) (k => splitsAt beams [l, ..rest] k)
          := Eq.sym (List.sumByRangeSucc (k => splitsAt beams [l, ..rest] k) rest.length)

--| At the start, the only beam is in S's column.
theorem beamStart (w: Nat) (st: Fin w) (ls: List (Vec Bool w)) (k: Nat) (d: Nat):
    beamReach (Vec.tabulate w (c => c == st)) ls k d = reach ls st.toNat k d :=
  let start := Vec.tabulate w (c => c == st)
  rewrite <- Fin.anyRange (c => start.getOr c False ∧ reach ls c k d) w, Vec.getOrGet start _ False, Vec.getTabulate w (c => c == st) _ in
    Fin.anyEqAnd st (c => reach ls c.toNat k d)

--| The splitters some timeline reaches in row k: those the beams reach.
theorem splitsAtReached (manifold: Manifold) (k: Nat):
    splitsAt (Vec.tabulate manifold.width (c => c == manifold.start)) manifold.rows k
      = List.count (List.range 0 manifold.width) (d => reached (timelines manifold) k d) :=
  let w := manifold.width
  let st := manifold.start.toNat
  let start := Vec.tabulate w (c => c == manifold.start)
  rewrite List.countSumBy (List.range 0 w) (d => reached (timelines manifold) k d), beamStart w manifold.start manifold.rows k _,
    <- hitsAt manifold.rows 0 st k _, Nat.addZero k

--| Part 1 is right: for every manifold, the printed answer is the number of
--| splitters some timeline of the particle from S reaches.
theorem part1Correct (manifold: Manifold): solvePart1 manifold = part1Spec manifold :=
  let start := Vec.tabulate manifold.width (c => c == manifold.start)
  calc splitsBelow start manifold.rows
    _ = List.sumBy (List.range 0 (List.length manifold.rows)) (k => splitsAt start manifold.rows k)
      := splitsBelowSum manifold.width manifold.rows start
    _ = List.sumBy (List.range 0 (List.length manifold.rows)) (k => List.count (List.range 0 manifold.width) (d => reached (timelines manifold) k d))
      := rewrite splitsAtReached manifold _
