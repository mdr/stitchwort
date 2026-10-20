namespace Aoc.Day06.Proofs
import Std (Eq)

theorem PList.lengthRangeFrom: (n: Nat) -> (s: Nat) -> List.length (List.rangeFrom n s) = n
  | Zero,   s => rfl
  | Succ n, s => rewrite PList.lengthRangeFrom n (Succ s)

theorem PList.mapMap (f: b -> c) (g: a -> b): (xs: List a) -> List.map f (List.map g xs) = List.map (x => f (g x)) xs
  | Nil       => rfl
  | Cons x xs => rewrite PList.mapMap f g xs

theorem PList.mapMaybeMap (f: b -> Maybe c) (g: a -> b): (xs: List a) -> List.mapMaybe f (List.map g xs) = List.mapMaybe (x => f (g x)) xs
  | Nil       => rfl
  | Cons x xs => rewrite PList.mapMaybeMap f g xs

theorem PList.mapMaybeJust (f: a -> b): (xs: List a) -> List.mapMaybe (x => Just (f x)) xs = List.map f xs
  | Nil       => rfl
  | Cons x xs => rewrite PList.mapMaybeJust f xs

theorem PList.mapMaybeAppend (f: a -> Maybe b): (xs: List a) -> (ys: List a) ->
    List.mapMaybe f (List.append xs ys) = List.append (List.mapMaybe f xs) (List.mapMaybe f ys)
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    match f x with
      | Nothing => PList.mapMaybeAppend f xs ys
      | Just y  => rewrite PList.mapMaybeAppend f xs ys

theorem PList.initMap (f: a -> b): (xs: List a) -> List.init (List.map f xs) = List.map f (List.init xs)
  | Nil                => rfl
  | Cons x Nil         => rfl
  | Cons x (Cons y ys) => rewrite PList.initMap f (Cons y ys)

theorem PList.lastMap (f: a -> b): (xs: List a) -> List.last (List.map f xs) = Maybe.map f (List.last xs)
  | Nil                => rfl
  | Cons x Nil         => rfl
  | Cons x (Cons y ys) => PList.lastMap f (Cons y ys)

theorem PList.getOrReplicate (x: a): (i: Nat) -> (n: Nat) -> List.getOr x i (List.replicate n x) = x
  | i,      Zero   => rfl
  | Zero,   Succ n => rfl
  | Succ i, Succ n => PList.getOrReplicate x i n

-- Copies of the default on the end change no index.
theorem PList.getOrAppendReplicate (x: a) (k: Nat): (i: Nat) -> (xs: List a) -> List.getOr x i (List.append xs (List.replicate k x)) = List.getOr x i xs
  | i,      Nil       => PList.getOrReplicate x i k
  | Zero,   Cons y ys => rfl
  | Succ i, Cons y ys => PList.getOrAppendReplicate x k i ys

theorem PList.getOrPadRight (x: a) (n: Nat) (i: Nat) (xs: List a): List.getOr x i (List.padRight n x xs) = List.getOr x i xs :=
  PList.getOrAppendReplicate x (n - List.length xs) i xs

-- Past the end, the default.
theorem PList.getOrPast (d: a): (i: Nat) -> (xs: List a) -> List.length xs <= i -> List.getOr d i xs = d
  | i,      Nil,       h => rfl
  | Zero,   Cons x xs, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ i, Cons x xs, h => PList.getOrPast d i xs h

theorem PList.mapRangeShift (f: Nat -> b): (n: Nat) -> (s: Nat) ->
    List.map f (List.rangeFrom n (Succ s)) = List.map (i => f (Succ i)) (List.rangeFrom n s)
  | Zero,   s => rfl
  | Succ n, s => rewrite PList.mapRangeShift f n (Succ s)

-- A list is its elements read off by index.
theorem PList.mapGetOr (d: a): (xs: List a) -> List.map (i => List.getOr d i xs) (List.range (List.length xs)) = xs
  | Nil       => rfl
  | Cons x xs =>
    calc List.map (i => List.getOr d i (Cons x xs)) (List.rangeFrom (Succ (List.length xs)) 0)
      _ = Cons x (List.map (i => List.getOr d i (Cons x xs)) (List.rangeFrom (List.length xs) 1))
      _ = Cons x (List.map (i => List.getOr d i xs) (List.rangeFrom (List.length xs) 0))
          := rewrite PList.mapRangeShift (i => List.getOr d i (Cons x xs)) (List.length xs) 0
      _ = Cons x xs := rewrite PList.mapGetOr d xs

-- Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem PList.transposeNGrid (cell: a -> b -> c) (rows: List a): (cols: List b) ->
    List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) rows) = List.map (y => List.map (x => cell x y) rows) cols
  | Nil         => rfl
  | Cons y cols =>
    calc List.transposeN (Succ (List.length cols)) (List.map (x => List.map (cell x) (Cons y cols)) rows)
      _ = Cons (List.mapMaybe (List.get 0) (List.map (x => List.map (cell x) (Cons y cols)) rows))
               (List.transposeN (List.length cols) (List.map (List.drop 1) (List.map (x => List.map (cell x) (Cons y cols)) rows)))
      _ = Cons (List.mapMaybe (x => Just (cell x y)) rows) (List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) rows))
          := rewrite PList.mapMaybeMap (List.get 0) (x => List.map (cell x) (Cons y cols)) rows,
                     PList.mapMap (List.drop 1) (x => List.map (cell x) (Cons y cols)) rows
      _ = Cons (List.map (x => cell x y) rows) (List.map (z => List.map (x => cell x z) rows) cols)
          := rewrite PList.mapMaybeJust (x => cell x y) rows, PList.transposeNGrid cell rows cols

theorem PList.transposeGrid (cell: a -> b -> c) (r: a) (rows: List a) (cols: List b):
    List.transpose (List.map (x => List.map (cell x) cols) (Cons r rows)) = List.map (y => List.map (x => cell x y) (Cons r rows)) cols :=
  calc List.transpose (List.map (x => List.map (cell x) cols) (Cons r rows))
    _ = List.transposeN (List.length (List.map (cell r) cols)) (List.map (x => List.map (cell x) cols) (Cons r rows))
    _ = List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) (Cons r rows)) := rewrite List.lengthMap (cell r) cols
    _ = List.map (y => List.map (x => cell x y) (Cons r rows)) cols := PList.transposeNGrid cell (Cons r rows) cols

-- Splitting a run of positions at the separators.

theorem PBool.andFalse: (b: Bool) -> (b && False) = False
  | True  => rfl
  | False => rfl

theorem PBool.andTrue: (b: Bool) -> (b && True) = b
  | True  => rfl
  | False => rfl

theorem PList.splitStepSep (x: a): (st: Pair (List a) (List (List a))) -> List.splitStep x True st = MkPair Nil (List.closeGroup (Pair.fst st) (Pair.snd st))
  | MkPair cur done => rfl

theorem PList.splitStepJoin (x: a): (st: Pair (List a) (List (List a))) -> List.splitStep x False st = MkPair (Cons x (Pair.fst st)) (Pair.snd st)
  | MkPair cur done => rfl

theorem PList.finishGroupsClose: (st: Pair (List a) (List (List a))) -> List.finishGroups st = List.closeGroup (Pair.fst st) (Pair.snd st)
  | MkPair cur done => rfl

-- The run from `s` up to the first separator (looking as far as `s + m`).
theorem PList.runStop (sep: Nat -> Bool) (m: Nat) (s: Nat) (h: sep s = True): Nat.firstFrom sep (Succ m) s - s = 0 :=
  rewrite Nat.firstFromStop sep m s h, Nat.subSelf s

theorem PList.runStep (sep: Nat -> Bool) (m: Nat) (s: Nat) (h: sep s = False):
    Nat.firstFrom sep (Succ m) s - s = Succ (Nat.firstFrom sep m (Succ s) - Succ s) :=
  rewrite Nat.firstFromSkip sep m s h in Nat.subSuccRight s (Nat.firstFrom sep m (Succ s)) (Nat.firstFromAtLeast sep m (Succ s))

-- The group still open after reading positions s .. s + m - 1 (from the
-- right) is the run from s to the first separator; s + m is a separator.
theorem PList.splitGroupsOpen (p: a -> Bool) (f: Nat -> a) (sep: Nat -> Bool) (hsep: (c: Nat) -> p (f c) = sep c):
    (m: Nat) -> (s: Nat) -> sep (s + m) = True ->
    Pair.fst (List.splitGroups p (List.map f (List.rangeFrom m s))) = List.map f (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s)
  | Zero,   s, e => rewrite PList.runStop sep 0 s (rewrite <- Nat.addZero s in e)
  | Succ m, s, e =>
    calc Pair.fst (List.splitStep (f s) (p (f s)) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))))
      _ = Pair.fst (List.splitStep (f s) (sep s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s))))) := rewrite hsep s
      _ = List.map f (List.rangeFrom (Nat.firstFrom sep (Succ (Succ m)) s - s) s) :=
          match h: sep s with
            | True  => rewrite PList.splitStepSep (f s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))), Nat.subSelf s
            | False =>
              rewrite PList.splitStepJoin (f s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))), Nat.subSuccRight s (Nat.firstFrom sep (Succ m) (Succ s)) (Nat.firstFromAtLeast sep (Succ m) (Succ s)),
                PList.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e)

theorem PNat.addSubLeft (s: Nat) (m: Nat): (s + m) - s = m := rewrite Nat.addComm s m in Nat.addSub m s

-- The run of positions from `lo` up to the first separator, looking no
-- further than `n`.
def PList.run (f: Nat -> a) (sep: Nat -> Bool) (n: Nat) (lo: Nat): List a :=
  List.map f (List.rangeFrom (Nat.firstFrom sep (Succ (n - lo)) lo - lo) lo)

-- Closing the open group adds its term, unless it is empty.
theorem PList.closeRunSum (f: Nat -> a) (sep: Nat -> Bool) (g: List a -> Nat) (done: List (List a)) (m: Nat) (s: Nat):
    List.sumBy g (List.closeGroup (List.map f (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s)) done)
      = Nat.keepIf (g (List.map f (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s))) (Bool.not (sep s)) + List.sumBy g done :=
  match h: sep s with
    | True  => rewrite Nat.subSelf s
    | False =>
      rewrite Nat.subSuccRight s (Nat.firstFrom sep m (Succ s)) (Nat.firstFromAtLeast sep m (Succ s)) in
        List.sumByCons g (Cons (f s) (List.map f (List.rangeFrom (Nat.firstFrom sep m (Succ s) - Succ s) (Succ s)))) done

-- The groups closed after reading positions s .. s + m - 1: one for every
-- separator c followed by a position c + 1 that isn't one.
theorem PList.splitGroupsDone (p: a -> Bool) (f: Nat -> a) (sep: Nat -> Bool) (hsep: (c: Nat) -> p (f c) = sep c) (g: List a -> Nat):
    (m: Nat) -> (s: Nat) -> sep (s + m) = True ->
    List.sumBy g (Pair.snd (List.splitGroups p (List.map f (List.rangeFrom m s))))
      = List.sumBy (c => Nat.keepIf (g (PList.run f sep (s + m) (Succ c))) (Bool.not (sep (Succ c)) && sep c)) (List.rangeFrom m s)
  | Zero,   s, e => rfl
  | Succ m, s, e =>
    calc List.sumBy g (Pair.snd (List.splitStep (f s) (p (f s)) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s))))))
      _ = List.sumBy g (Pair.snd (List.splitStep (f s) (sep s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))))) := rewrite hsep s
      _ = Nat.keepIf (g (PList.run f sep (Succ (s + m)) (Succ s))) (Bool.not (sep (Succ s)) && sep s)
            + List.sumBy (c => Nat.keepIf (g (PList.run f sep (Succ (s + m)) (Succ c))) (Bool.not (sep (Succ c)) && sep c)) (List.rangeFrom m (Succ s)) :=
          match h: sep s with
            | True  =>
              rewrite PList.splitStepSep (f s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))),
                PList.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e),
                PList.closeRunSum f sep g (Pair.snd (List.splitGroups p (List.map f (List.rangeFrom m (Succ s))))) m (Succ s),
                PList.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
                PBool.andTrue (Bool.not (sep (Succ s))), PNat.addSubLeft s m
            | False =>
              rewrite PList.splitStepJoin (f s) (List.splitGroups p (List.map f (List.rangeFrom m (Succ s)))),
                PList.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
                PBool.andFalse (Bool.not (sep (Succ s)))
      _ = List.sumBy (c => Nat.keepIf (g (PList.run f sep (s + Succ m) (Succ c))) (Bool.not (sep (Succ c)) && sep c)) (List.rangeFrom (Succ m) s) :=
          rewrite Nat.addSucc s m in
            Eq.sym (List.sumByCons (c => Nat.keepIf (g (PList.run f sep (Succ (s + m)) (Succ c))) (Bool.not (sep (Succ c)) && sep c)) s (List.rangeFrom m (Succ s)))

-- All the groups: the run from 0, then one for every separator followed by
-- a position that isn't one.
theorem PList.splitByStarts (p: a -> Bool) (f: Nat -> a) (sep: Nat -> Bool) (hsep: (c: Nat) -> p (f c) = sep c) (g: List a -> Nat) (n: Nat) (end: sep n = True):
    List.sumBy g (List.splitBy p (List.map f (List.range n)))
      = Nat.keepIf (g (PList.run f sep n 0)) (Bool.not (sep 0))
        + List.sumBy (c => Nat.keepIf (g (PList.run f sep n (Succ c))) (Bool.not (sep (Succ c)) && sep c)) (List.range n) :=
  rewrite PList.finishGroupsClose (List.splitGroups p (List.map f (List.rangeFrom n 0))),
    PList.splitGroupsOpen p f sep hsep n 0 end,
    PList.closeRunSum f sep g (Pair.snd (List.splitGroups p (List.map f (List.rangeFrom n 0)))) n 0,
    PList.splitGroupsDone p f sep hsep g n 0 end

-- `lo .. hi - 1` is a maximal run of positions that aren't separators: the
-- one before it is a separator (or lo is 0), it isn't empty, none in it is a
-- separator, and hi is one.
def PNat.isRun (sep: Nat -> Bool) (lo: Nat) (hi: Nat): Bool :=
  (lo == 0 || sep (lo - 1)) && (lo < hi && (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi))

theorem PList.isRunNoEdge (sep: Nat -> Bool) (lo: Nat) (hi: Nat) (h: (lo == 0 || sep (lo - 1)) = False): PNat.isRun sep lo hi = False :=
  calc PNat.isRun sep lo hi
    _ = ((lo == 0 || sep (lo - 1)) && (lo < hi && (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi)))
    _ = False := rewrite h

theorem PList.isRunSepStart (sep: Nat -> Bool) (lo: Nat) (hi: Nat) (h: sep lo = True): PNat.isRun sep lo hi = False :=
  calc PNat.isRun sep lo hi
    _ = ((lo == 0 || sep (lo - 1)) && (lo < hi && (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi)))
    _ = ((lo == 0 || sep (lo - 1)) && False) :=
        match e: Nat.leq (Succ lo) hi with
          | False => rfl
          | True  => rewrite Nat.subSuccRight lo hi e, h
    _ = False := PBool.andFalse (lo == 0 || sep (lo - 1))

-- A run that starts at lo ends at the first separator after it.
theorem PList.isRunEnd (sep: Nat -> Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True) (hi: Nat) (h: PNat.isRun sep lo hi = True):
    hi = Nat.firstFrom sep (Succ (n - lo)) lo :=
  let rest := Bool.andRight (lo == 0 || sep (lo - 1)) (lo < hi && (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi)) h
  let long: Succ lo <= hi := rewrite <- Bool.decTrueToBool (Nat.leq (Succ lo) hi) in
                               Bool.andLeft (lo < hi) (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi) rest
  let inner := Bool.andRight (lo < hi) (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo) && sep hi) rest
  let none := Bool.andLeft (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo)) (sep hi) inner
  let stop := Bool.andRight (List.all (c => Bool.not (sep c)) (List.rangeFrom (hi - lo) lo)) (sep hi) inner
  let found := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
                 (rewrite Nat.addSucc lo (n - lo), Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  match e: Nat.leq hi (Nat.firstFrom sep (Succ (n - lo)) lo) with
    | True  => Nat.leAntisym hi (Nat.firstFrom sep (Succ (n - lo)) lo) e (Nat.firstFromLe sep (Succ (n - lo)) lo hi (Nat.lessLe lo hi long) stop)
    | False =>
      Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym found)
        (calc sep (Nat.firstFrom sep (Succ (n - lo)) lo)
          _ = Bool.not (Bool.not (sep (Nat.firstFrom sep (Succ (n - lo)) lo))) := match sep (Nat.firstFrom sep (Succ (n - lo)) lo) with | True => rfl | False => rfl
          _ = False := rewrite List.allRangeElim (c => Bool.not (sep c)) (hi - lo) lo none (Nat.firstFrom sep (Succ (n - lo)) lo)
                         (Nat.firstFromAtLeast sep (Succ (n - lo)) lo)
                         (rewrite Nat.addSubCancel lo hi (Nat.lessLe lo hi long) in Nat.leqFalse hi (Nat.firstFrom sep (Succ (n - lo)) lo) e))))

-- The run that starts at lo (it does start there) is a maximal run.
theorem PList.isRunRun (sep: Nat -> Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True)
    (h1: sep lo = False) (h2: (lo == 0 || sep (lo - 1)) = True): PNat.isRun sep lo (Nat.firstFrom sep (Succ (n - lo)) lo) = True :=
  let v := Nat.firstFrom sep (Succ (n - lo)) lo
  let found: sep v = True := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
                 (rewrite Nat.addSucc lo (n - lo), Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  let atLeast: lo <= v := Nat.firstFromAtLeast sep (Succ (n - lo)) lo
  let long: Succ lo <= v := Nat.leNeSucc lo v atLeast (e => Bool.falseNotTrue (Eq.trans (Eq.sym h1) (rewrite e in found)))
  Bool.andIntro (lo == 0 || sep (lo - 1)) (lo < v && (List.all (c => Bool.not (sep c)) (List.rangeFrom (v - lo) lo) && sep v)) h2
    (Bool.andIntro (lo < v) (List.all (c => Bool.not (sep c)) (List.rangeFrom (v - lo) lo) && sep v) (rewrite Bool.decTrueToBool (Nat.leq (Succ lo) v) in long)
      (Bool.andIntro (List.all (c => Bool.not (sep c)) (List.rangeFrom (v - lo) lo)) (sep v)
        (List.allRangeIntro (c => Bool.not (sep c)) (v - lo) lo (k k1 k2 =>
          rewrite Nat.firstFromBefore sep (Succ (n - lo)) lo k k1 (rewrite <- Nat.addSubCancel lo v atLeast in k2)))
        found))

theorem PList.runsFromEdge (sep: Nat -> Bool) (f: Nat -> a) (g: List a -> Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n) (h1: sep lo = False):
    (b: Bool) -> (lo == 0 || sep (lo - 1)) = b ->
    List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))
      = Nat.keepIf (g (PList.run f sep n lo)) b
  | False, h2 => List.sumRangeNone (hi => PNat.isRun sep lo hi) (hi => g (List.map f (List.rangeFrom (hi - lo) lo))) (Succ n) 0
                   (b b1 b2 => PList.isRunNoEdge sep lo b h2)
  | True,  h2 =>
    List.sumRangeOne (hi => PNat.isRun sep lo hi) (hi => g (List.map f (List.rangeFrom (hi - lo) lo)))
      (Nat.firstFrom sep (Succ (n - lo)) lo) (PList.isRunRun sep n lo hlo end h1 h2)
      (PList.isRunEnd sep n lo hlo end) (Succ n) 0 (Nat.zeroLe (Nat.firstFrom sep (Succ (n - lo)) lo))
      (Nat.firstFromLe sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo) end)

-- For each lo, the maximal runs starting there: one if a run starts at lo, none otherwise.
theorem PList.runsFrom (sep: Nat -> Bool) (f: Nat -> a) (g: List a -> Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n):
    List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))
      = Nat.keepIf (g (PList.run f sep n lo)) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1))) :=
  PList.runsFromStart sep f g n end lo hlo (sep lo) rfl

theorem PList.runsFromStart (sep: Nat -> Bool) (f: Nat -> a) (g: List a -> Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n):
    (b: Bool) -> sep lo = b ->
    List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))
      = Nat.keepIf (g (PList.run f sep n lo)) (Bool.not b && (lo == 0 || sep (lo - 1)))
  | True,  h1 => List.sumRangeNone (hi => PNat.isRun sep lo hi) (hi => g (List.map f (List.rangeFrom (hi - lo) lo))) (Succ n) 0
                   (b b1 b2 => PList.isRunSepStart sep lo b h1)
  | False, h1 => PList.runsFromEdge sep f g n end lo hlo h1 (lo == 0 || sep (lo - 1)) rfl

theorem PList.sumRangeLast (f: Nat -> Nat) (n: Nat): List.sumBy f (List.range (Succ n)) = List.sumBy f (List.range n) + f n :=
  calc List.sumBy f (List.rangeFrom (Succ n) 0)
    _ = List.sumBy f (List.append (List.rangeFrom n 0) (List.rangeFrom 1 (0 + n))) := rewrite <- List.rangeFromAppend n 1 0, Nat.addOne n
    _ = List.sumBy f (List.range n) + f n := List.sumByAppend f (List.rangeFrom n 0) (List.rangeFrom 1 n)

-- The runs by where they start: at 0, or just after a separator.
theorem PList.runStarts (sep: Nat -> Bool) (r: Nat -> Nat): (n: Nat) -> sep n = True ->
    List.sumBy (lo => Nat.keepIf (r lo) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) (List.range n)
      = Nat.keepIf (r 0) (Bool.not (sep 0)) + List.sumBy (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) (List.range n)
  | Zero,   end => rewrite end
  | Succ n, end =>
    calc List.sumBy (lo => Nat.keepIf (r lo) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) (List.rangeFrom (Succ n) 0)
      _ = Nat.keepIf (r 0) (Bool.not (sep 0) && True)
            + List.sumBy (lo => Nat.keepIf (r lo) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) (List.rangeFrom n 1)
          := List.sumByCons (lo => Nat.keepIf (r lo) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) 0 (List.rangeFrom n 1)
      _ = Nat.keepIf (r 0) (Bool.not (sep 0)) + List.sumBy (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) (List.range n)
          := rewrite PBool.andTrue (Bool.not (sep 0)), List.sumByRangeShift (lo => Nat.keepIf (r lo) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) n 0
      _ = Nat.keepIf (r 0) (Bool.not (sep 0)) + (List.sumBy (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) (List.range n) + 0)
          := rewrite Nat.addZero (List.sumBy (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) (List.range n))
      _ = Nat.keepIf (r 0) (Bool.not (sep 0)) + List.sumBy (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) (List.range (Succ n))
          := rewrite PList.sumRangeLast (c => Nat.keepIf (r (Succ c)) (Bool.not (sep (Succ c)) && sep c)) n, end

-- Splitting the positions 0 .. n - 1 at the separators gives exactly the
-- maximal runs `lo .. hi - 1` (`PNat.isRun`), when position n is a separator.
theorem PList.splitByRuns (p: a -> Bool) (f: Nat -> a) (sep: Nat -> Bool) (hsep: (c: Nat) -> p (f c) = sep c) (g: List a -> Nat) (n: Nat) (end: sep n = True):
    List.sumBy g (List.splitBy p (List.map f (List.range n)))
      = List.sumBy (lo => List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))) (List.range n) :=
  calc List.sumBy g (List.splitBy p (List.map f (List.range n)))
    _ = Nat.keepIf (g (PList.run f sep n 0)) (Bool.not (sep 0))
          + List.sumBy (c => Nat.keepIf (g (PList.run f sep n (Succ c))) (Bool.not (sep (Succ c)) && sep c)) (List.range n)
        := PList.splitByStarts p f sep hsep g n end
    _ = List.sumBy (lo => Nat.keepIf (g (PList.run f sep n lo)) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1)))) (List.range n)
        := Eq.sym (PList.runStarts sep (lo => g (PList.run f sep n lo)) n end)
    _ = List.sumBy (lo => List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))) (List.range n)
        := List.sumRangeCongr (lo => Nat.keepIf (g (PList.run f sep n lo)) (Bool.not (sep lo) && (lo == 0 || sep (lo - 1))))
             (lo => List.sumBy (hi => Nat.keepIf (g (List.map f (List.rangeFrom (hi - lo) lo))) (PNat.isRun sep lo hi)) (List.range (Succ n))) n 0
             (lo l1 l2 => Eq.sym (PList.runsFrom sep f g n end lo l2))

-- Digit characters read back as their digits.
theorem PChar.digitValueChar: (d: Nat) -> Nat.leq d 9 = True -> Char.digitValue (Nat.digitChar d) = Just d
  | 0, h => rfl
  | 1, h => rfl
  | 2, h => rfl
  | 3, h => rfl
  | 4, h => rfl
  | 5, h => rfl
  | 6, h => rfl
  | 7, h => rfl
  | 8, h => rfl
  | 9, h => rfl
  | Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ d))))))))), h => Void.exfalso (Bool.falseNotTrue h)

theorem PChar.digitsOntoValues: (f: Nat) -> (n: Nat) -> (acc: List Char) -> n < f ->
    List.mapMaybe Char.digitValue (Nat.digitsOnto f n acc) = Nat.digitsFuel f n (List.mapMaybe Char.digitValue acc)
  | Zero,   n, acc, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ f, n, acc, h =>
    match e: Nat.leq n 9 with
      | True  => rewrite PChar.digitValueChar n e
      | False =>
        calc List.mapMaybe Char.digitValue (Nat.digitsOnto f (n / 10) (Cons (Nat.digitChar (n % 10)) acc))
          _ = Nat.digitsFuel f (n / 10) (List.mapMaybe Char.digitValue (Cons (Nat.digitChar (n % 10)) acc))
              := PChar.digitsOntoValues f (n / 10) (Cons (Nat.digitChar (n % 10)) acc) (Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n e) h)
          _ = Nat.digitsFuel f (n / 10) (Cons (n % 10) (List.mapMaybe Char.digitValue acc)) := rewrite PChar.digitValueChar (n % 10) (Nat.modLt n 10)

-- A number written in decimal reads back as its digits.
theorem PChar.toTextDigits (n: Nat): List.mapMaybe Char.digitValue (Text.toList (Nat.toText n)) = Nat.digits n :=
  PChar.digitsOntoValues (Succ n) n Nil (Nat.leRefl n)

theorem PList.mapReverseOnto (f: a -> b): (xs: List a) -> (acc: List a) ->
    List.map f (List.reverseOnto xs acc) = List.reverseOnto (List.map f xs) (List.map f acc)
  | Nil,       acc => rfl
  | Cons x xs, acc => PList.mapReverseOnto f xs (Cons x acc)

theorem PList.mapReverse (f: a -> b) (xs: List a): List.map f (List.reverse xs) = List.reverse (List.map f xs) := PList.mapReverseOnto f xs Nil

theorem PList.sumReverse (xs: List Nat): List.sum (List.reverse xs) = List.sum xs := List.sumByReverse (x => x) xs

theorem PNat.oneMul (n: Nat): 1 * n = n := Nat.addZero n

theorem PList.productFrom: (a: Nat) -> (xs: List Nat) -> List.foldLeft Nat.mul a xs = a * List.product xs
  | a, Nil       => Eq.sym (Nat.mulOne a)
  | a, Cons x xs =>
    calc List.foldLeft Nat.mul (a * x) xs
      _ = (a * x) * List.product xs := PList.productFrom (a * x) xs
      _ = a * (x * List.product xs) := Nat.mulAssoc a x (List.product xs)
      _ = a * List.foldLeft Nat.mul (1 * x) xs := rewrite PList.productFrom (1 * x) xs, PNat.oneMul x

theorem PList.productCons (x: Nat) (xs: List Nat): List.product (Cons x xs) = x * List.product xs :=
  rewrite PList.productFrom (1 * x) xs, PNat.oneMul x

theorem PList.productReverseOnto: (xs: List Nat) -> (acc: List Nat) -> List.product (List.reverseOnto xs acc) = List.product xs * List.product acc
  | Nil,       acc => Eq.sym (PNat.oneMul (List.product acc))
  | Cons x xs, acc =>
    calc List.product (List.reverseOnto xs (Cons x acc))
      _ = List.product xs * (x * List.product acc) := rewrite PList.productReverseOnto xs (Cons x acc), PList.productCons x acc
      _ = (x * List.product xs) * List.product acc
          := rewrite <- Nat.mulAssoc (List.product xs) x (List.product acc), Nat.mulComm (List.product xs) x
      _ = List.product (Cons x xs) * List.product acc := rewrite PList.productCons x xs

theorem PList.productReverse (xs: List Nat): List.product (List.reverse xs) = List.product xs :=
  rewrite PList.productReverseOnto xs Nil in Nat.mulOne (List.product xs)

theorem PList.mapMaybeCongr (f: a -> Maybe b) (g: a -> Maybe b) (h: (x: a) -> f x = g x): (xs: List a) -> List.mapMaybe f xs = List.mapMaybe g xs
  | Nil       => rfl
  | Cons x xs => rewrite h x, PList.mapMaybeCongr f g h xs

theorem PMaybe.andThenMap (g: b -> Maybe c) (f: a -> b): (m: Maybe a) -> Maybe.andThen g (Maybe.map f m) = Maybe.andThen (x => g (f x)) m
  | Nothing => rfl
  | Just x  => rfl
