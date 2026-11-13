--| `List.splitBy`, which cuts a list at its separators into `NonEmptyList` groups,
--| and the lemmas about it: the groups have no separator, they keep the other
--| elements in order, and the lengths and sums of the groups of a run of positions.
-- Its own file, not part of List/Toolkit.sw, because the groups are
-- `NonEmptyList`s and NonEmptyList/NonEmptyList.sw needs the sorting lemmas,
-- which need the toolkit.

--| The groups of consecutive elements that don't satisfy `p`, in order: `p`
--| marks the separators, which are dropped, and no group is empty (each is a
--| `NonEmptyList`; there may be no groups at all). So
--| `List.splitBy [1, 2, 0, 0, 3] (x => x == 0)` is `[[1, 2], [3]]`. No group
--| has a separator ([`List.splitByGroups`]), and the groups
--| joined are the elements that aren't separators ([`List.splitByConcat`]).
def List.splitBy (xs: List a) (p: a → Bool): List (NonEmptyList a) := List.finishGroups (List.splitGroups xs p)

--| Reads the list from the right: the group still open at the front, and the
--| groups finished after it. A right fold, so it runs as a loop over the
--| reversed list (stack-safe on long lists); [`List.splitGroupsCons`] is its step.
def List.splitGroups (xs: List a) (p: a → Bool): Pair (List a) (List (NonEmptyList a)) :=
  List.foldRight xs (MkPair [] []) (x st => List.splitStep x (p x) st)

--| Adds the element `x` in front: a separator (`True`) closes the open group,
--| anything else joins it.
def List.splitStep (x: a): (isSeparator: Bool) → (groups: Pair (List a) (List (NonEmptyList a))) → Pair (List a) (List (NonEmptyList a))
  | True, MkPair cur done => MkPair [] (List.closeGroup cur done)
  | False, MkPair cur done => MkPair [x, ..cur] done

--| The groups of `List.splitBy`, with the group still open closed.
def List.finishGroups: (groups: Pair (List a) (List (NonEmptyList a))) → List (NonEmptyList a)
  | MkPair cur done => List.closeGroup cur done

--| Adds a group to the finished ones, unless it is empty.
def List.closeGroup: (current: List a) → (done: List (NonEmptyList a)) → List (NonEmptyList a)
  | [], done => done
  | [y, ..ys], done => [[y, ..ys], ..done]

--| How many elements a state of `List.splitBy` holds, in the open group and the finished ones.
def List.splitTotal (st: Pair (List a) (List (NonEmptyList a))): Nat := List.length (Pair.fst st) + List.sumBy (Pair.snd st) NonEmptyList.length

--| The group has no separator in it.
@[noReceiver]
def List.NonSep (p: a → Bool) (g: List a): Prop := List.all g (x => ¬(p x)) = True

--| No group has a separator in it.
@[noReceiver]
def List.Groups (p: a → Bool): (groups: List (NonEmptyList a)) → Prop
  | [] => Unit
  | [g, ..gs] => (List.NonSep p g.toList) ∧ (List.Groups p gs)

--| A state of `List.splitBy` is well formed: no group, open or finished, has a separator in it.
def List.SplitOk (p: a → Bool): (groups: Pair (List a) (List (NonEmptyList a))) → Prop
  | MkPair cur done => (List.NonSep p cur) ∧ (List.Groups p done)

--| A state of `List.splitBy` holds exactly the elements of `xs` that aren't separators, in order.
@[noReceiver]
def List.SplitKeeps (p: a → Bool) (xs: List a) (st: Pair (List a) (List (NonEmptyList a))): Prop :=
  List.append (Pair.fst st) (List.flatMap (Pair.snd st) NonEmptyList.toList) = List.filter xs (x => ¬(p x))

test "List.splitBy with separators on the end" :=
  ([1, 0, 2].splitBy (== 0)).map NonEmptyList.toList == [[1], [2]] ∧ ([1, 0, 2, 0, 0].splitBy (== 0)).map NonEmptyList.toList == [[1], [2]] ∧
    ([0, 0].splitBy (== 0)).map NonEmptyList.toList == []

--| The step of `List.splitGroups`, which the loop form hides.
theorem List.splitGroupsCons ∀ (xs: List a) (x: a) (p: a → Bool):
    List.splitGroups [x, ..xs] p = List.splitStep x (p x) (List.splitGroups xs p) :=
  List.foldRightCons xs x (MkPair [] []) (y st => List.splitStep y (p y) st)

theorem List.closeGroupSum ∀ (cur: List a) (done: List (NonEmptyList a)):
    List.sumBy (List.closeGroup cur done) NonEmptyList.length = List.length cur + List.sumBy done NonEmptyList.length :=
  match cur with
    | [] => rfl
    | [y, ..ys] => List.sumByCons done [y, ..ys] NonEmptyList.length

theorem List.splitStepTotal ∀ (x: a) (b: Bool) (st: Pair (List a) (List (NonEmptyList a))):
    List.splitTotal (List.splitStep x b st) + Bool.toNat b = Succ (List.splitTotal st) := match b, st with
      | True, MkPair cur done =>
        Eq.trans (Nat.addOne (List.sumBy (List.closeGroup cur done) NonEmptyList.length)) (Eq.cong Succ (List.closeGroupSum cur done))
      | False, MkPair cur done => Nat.addZero (Succ (List.length cur + List.sumBy done NonEmptyList.length))

theorem List.splitGroupsTotal ∀ (xs: List a) (p: a → Bool):
    List.splitTotal (List.splitGroups xs p) + List.occurrences xs p = List.length xs := match xs with
      | [] => rfl
      | [x, ..xs] =>
        rewrite List.splitGroupsCons xs x p in
          Eq.trans (Eq.sym (Nat.addAssoc (List.splitTotal (List.splitStep x (p x) (List.splitGroups xs p))) (Bool.toNat (p x)) (List.occurrences xs p)))
            (Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.splitStepTotal x (p x) (List.splitGroups xs p)))
              (Eq.cong Succ (List.splitGroupsTotal xs p)))

theorem List.finishGroupsSum ∀ (st: Pair (List a) (List (NonEmptyList a))):
    List.sumBy (List.finishGroups st) NonEmptyList.length = List.splitTotal st := match st with
      | MkPair cur done => List.closeGroupSum cur done

--| `[1, 2, 0, 0, 3]` split at its zeros is `[[1, 2], [3]]`.
theorem List.splitByExample: List.splitBy [1, 2, 0, 0, 3] (x => x == 0) = [[1, 2], [3]] := rfl

theorem List.splitByEdges: List.splitBy [0, 4, 0] (x => x == 0) = [[4]] := rfl

--| Splitting loses only the separators: the groups' lengths plus the number of separators is the length.
theorem List.splitByLength ∀ (xs: List a) (p: a → Bool):
    List.sumBy (List.splitBy xs p) NonEmptyList.length + List.occurrences xs p = List.length xs :=
  Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.finishGroupsSum (List.splitGroups xs p))) (List.splitGroupsTotal xs p)

theorem List.closeGroupGroups ∀ (p: a → Bool) (cur: List a) (done: List (NonEmptyList a)) (hc: List.NonSep p cur) (hd: List.Groups p done):
    List.Groups p (List.closeGroup cur done) := match cur with
      | [] => hd
      | [y, ..ys] => Both hc hd

theorem List.nonSepCons ∀ (p: a → Bool) (x: a) (cur: List a) (h: p x = False) (hc: List.NonSep p cur): List.NonSep p [x, ..cur] :=
  rewrite h in hc

theorem List.splitStepOk ∀ (p: a → Bool) (x: a): ∀ (b: Bool) => p x = b → ∀ (st: Pair (List a) (List (NonEmptyList a))) => List.SplitOk p st →
    List.SplitOk p (List.splitStep x b st)
  | True, e, MkPair cur done, Both hc hd => Both rfl (List.closeGroupGroups p cur done hc hd)
  | False, e, MkPair cur done, Both hc hd => Both (List.nonSepCons p x cur e hc) hd

theorem List.splitGroupsOk ∀ (xs: List a) (p: a → Bool): List.SplitOk p (List.splitGroups xs p) := match xs with
  | [] => Both rfl Trivial
  | [x, ..xs] =>
    rewrite List.splitGroupsCons xs x p in List.splitStepOk p x (p x) rfl (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.finishGroupsOk ∀ (p: a → Bool) (st: Pair (List a) (List (NonEmptyList a))) (h: List.SplitOk p st): List.Groups p (List.finishGroups st) :=
  match st, h with
    | MkPair cur done, Both hc hd => List.closeGroupGroups p cur done hc hd

--| No group has a separator in it.
theorem List.splitByGroups ∀ (xs: List a) (p: a → Bool): List.Groups p (List.splitBy xs p) :=
  List.finishGroupsOk p (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.closeGroupConcat ∀ (cur: List a) (done: List (NonEmptyList a)):
    List.flatMap (List.closeGroup cur done) NonEmptyList.toList = List.append cur (List.flatMap done NonEmptyList.toList) :=
  match cur with
    | [] => rfl
    | [y, ..ys] => rfl

theorem List.splitStepKeeps ∀ (p: a → Bool) (x: a) (xs: List a): ∀ (b: Bool) => p x = b → ∀ (st: Pair (List a) (List (NonEmptyList a))) =>
    List.SplitKeeps p xs st → List.SplitKeeps p [x, ..xs] (List.splitStep x b st)
  | True, e, MkPair cur done, h =>
    Eq.trans (List.closeGroupConcat cur done)
      (Eq.trans h (Eq.sym (List.filterSkip xs (z => ¬(p z)) x (Eq.cong Bool.not e))))
  | False, e, MkPair cur done, h =>
    Eq.trans (Eq.cong (Cons x) h) (Eq.sym (List.filterKeep xs (z => ¬(p z)) x (Eq.cong Bool.not e)))

theorem List.splitGroupsKeeps ∀ (xs: List a) (p: a → Bool): List.SplitKeeps p xs (List.splitGroups xs p) :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      rewrite List.splitGroupsCons xs x p in List.splitStepKeeps p x xs (p x) rfl (List.splitGroups xs p) (List.splitGroupsKeeps xs p)

theorem List.finishGroupsConcat ∀ (st: Pair (List a) (List (NonEmptyList a))):
    List.flatMap (List.finishGroups st) NonEmptyList.toList = List.append (Pair.fst st) (List.flatMap (Pair.snd st) NonEmptyList.toList) :=
  match st with
    | MkPair cur done => List.closeGroupConcat cur done

--| Joining the groups gives back the elements that aren't separators, in order.
theorem List.splitByConcat ∀ (xs: List a) (p: a → Bool):
    List.flatMap (List.splitBy xs p) NonEmptyList.toList = List.filter xs (x => ¬(p x)) :=
  Eq.trans (List.finishGroupsConcat (List.splitGroups xs p)) (List.splitGroupsKeeps xs p)

--| Only separators: no group, open or finished.
theorem List.splitGroupsSeparators ∀ (ys: List a) (p: a → Bool) (h: List.all ys p = True): List.splitGroups ys p = MkPair [] [] :=
  match ys with
    | [] => rfl
    | [y, ..ys] =>
      match e: p y with
        | True => rewrite List.splitGroupsCons ys y p, e, List.splitGroupsSeparators ys p h

theorem List.splitGroupsAppendSeparators ∀ (ys: List a) (p: a → Bool) (h: List.all ys p = True) (xs: List a):
    List.splitGroups (List.append xs ys) p = List.splitGroups xs p := match xs with
      | [] => List.splitGroupsSeparators ys p h
      | [x, ..xs] => rewrite List.splitGroupsCons (List.append xs ys) x p, List.splitGroupsCons xs x p, List.splitGroupsAppendSeparators ys p h xs

--| Separators on the end change no group: `[1, 0, 0]` splits as `[1]` does.
theorem List.splitByAppendSeparators ∀ (xs: List a) (p: a → Bool) (ys: List a) (h: List.all ys p = True):
    List.splitBy (List.append xs ys) p = List.splitBy xs p :=
  Eq.cong List.finishGroups (List.splitGroupsAppendSeparators ys p h xs)

-- Splitting a run of positions at the separators.

theorem List.splitStepSep ∀ (x: a) (st: Pair (List a) (List (NonEmptyList a))): List.splitStep x True st = MkPair [] (List.closeGroup (Pair.fst st) (Pair.snd st)) :=
  match st with
    | MkPair cur done => rfl

theorem List.splitStepJoin ∀ (x: a) (st: Pair (List a) (List (NonEmptyList a))): List.splitStep x False st = MkPair [x, ..Pair.fst st] (Pair.snd st) :=
  match st with
    | MkPair cur done => rfl

theorem List.finishGroupsClose ∀ (st: Pair (List a) (List (NonEmptyList a))): List.finishGroups st = List.closeGroup (Pair.fst st) (Pair.snd st) :=
  match st with
    | MkPair cur done => rfl

--| The run from `s` up to the first separator (looking as far as `s + m`).
theorem List.runStop ∀ (sep: Nat → Bool) (m: Nat) (s: Nat) (h: sep s = True): Nat.firstFrom sep (Succ m) s - s = 0 :=
  rewrite Nat.firstFromStop sep m s h, Nat.subSelf s

--| The group still open after reading positions s .. s + m - 1 (from the
--| right) is the run from s to the first separator; s + m is a separator.
theorem List.splitGroupsOpen ∀ (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: ∀ (c: Nat) => p (f c) = sep c)
    (m s: Nat) (e: sep (s + m) = True):
    Pair.fst (List.splitGroups (List.map (List.rangeFrom m s) f) p) = List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f :=
  match m with
    | Zero => rewrite List.runStop sep 0 s (rewrite <- Nat.addZero s in e)
    | Succ m =>
      calc Pair.fst (List.splitGroups (List.map (List.rangeFrom (Succ m) s) f) p)
        _ = Pair.fst (List.splitStep (f s) (p (f s)) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))
          := Eq.cong Pair.fst (List.splitGroupsCons (List.map (List.rangeFrom m (Succ s)) f) (f s) p)
        _ = Pair.fst (List.splitStep (f s) (sep s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p)) := rewrite hsep s
        _ = List.map (List.rangeFrom (Nat.firstFrom sep (Succ (Succ m)) s - s) s) f :=
          match h: sep s with
            | True => rewrite List.splitStepSep (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p), Nat.subSelf s
            | False =>
              rewrite List.splitStepJoin (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p), Nat.subSuccRight s (Nat.firstFrom sep (Succ m) (Succ s)) (Nat.firstFromAtLeast sep (Succ m) (Succ s)),
                List.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e)

--| The run of positions from `lo` up to the first separator, looking no
--| further than `n`.
def List.runAt (f: Nat → a) (sep: Nat → Bool) (n: Nat) (lo: Nat): List a :=
  List.map (List.rangeFrom (Nat.firstFrom sep (Succ (n - lo)) lo - lo) lo) f

--| Closing the open group adds its term, unless it is empty.
theorem List.closeRunSum ∀ (g: List a → Nat) (done: List (NonEmptyList a)) (m: Nat) (s: Nat) (f: Nat → a) (sep: Nat → Bool):
    List.sumBy (List.closeGroup (List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f) done) (group => g group.toList)
      = Nat.keepIf (g (List.map (List.rangeFrom (Nat.firstFrom sep (Succ m) s - s) s) f)) (¬(sep s)) + List.sumBy done (group => g group.toList) :=
  match h: sep s with
    | True => rewrite Nat.subSelf s
    | False =>
      rewrite Nat.subSuccRight s (Nat.firstFrom sep m (Succ s)) (Nat.firstFromAtLeast sep m (Succ s)) in
        List.sumByCons done [f s, ..List.map (List.rangeFrom (Nat.firstFrom sep m (Succ s) - Succ s) (Succ s)) f] (group => g group.toList)

--| The groups closed after reading positions s .. s + m - 1: one for every
--| separator c followed by a position c + 1 that isn't one.
theorem List.splitGroupsDone ∀ (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: ∀ (c: Nat) => p (f c) = sep c) (g: List a → Nat)
    (m s: Nat) (e: sep (s + m) = True): List.sumBy (Pair.snd (List.splitGroups (List.map (List.rangeFrom m s) f) p)) (group => g group.toList)
      = List.sumBy (List.rangeFrom m s) (c => Nat.keepIf (g (List.runAt f sep (s + m) (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
  match m with
    | Zero => rfl
    | Succ m =>
      calc List.sumBy (Pair.snd (List.splitGroups (List.map (List.rangeFrom (Succ m) s) f) p)) (group => g group.toList)
        _ = List.sumBy (Pair.snd (List.splitStep (f s) (p (f s)) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))) (group => g group.toList)
          := Eq.cong (st => List.sumBy (Pair.snd st) (group => g group.toList)) (List.splitGroupsCons (List.map (List.rangeFrom m (Succ s)) f) (f s) p)
        _ = List.sumBy (Pair.snd (List.splitStep (f s) (sep s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p))) (group => g group.toList) := rewrite hsep s
        _ = Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ s))) (¬(sep (Succ s)) ∧ sep s)
            + List.sumBy (List.rangeFrom m (Succ s)) (c => Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
          match h: sep s with
            | True =>
              rewrite List.splitStepSep (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p),
                List.splitGroupsOpen p f sep hsep m (Succ s) (rewrite <- Nat.addSucc s m in e),
                List.closeRunSum g (Pair.snd (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p)) m (Succ s) f sep,
                List.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
                Bool.andTrue (¬(sep (Succ s))), Nat.addSubLeft s m
            | False =>
              rewrite List.splitStepJoin (f s) (List.splitGroups (List.map (List.rangeFrom m (Succ s)) f) p),
                List.splitGroupsDone p f sep hsep g m (Succ s) (rewrite <- Nat.addSucc s m in e),
                Bool.andFalse (¬(sep (Succ s)))
        _ = List.sumBy (List.rangeFrom (Succ m) s) (c => Nat.keepIf (g (List.runAt f sep (s + Succ m) (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
          Eq.sym (List.sumByCons (List.rangeFrom m (Succ s)) s (c => Nat.keepIf (g (List.runAt f sep (Succ (s + m)) (Succ c))) (¬(sep (Succ c)) ∧ sep c)))

--| All the groups: the run from 0, then one for every separator followed by
--| a position that isn't one.
theorem List.splitByStarts ∀ (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: ∀ (c: Nat) => p (f c) = sep c) (g: List a → Nat) (n: Nat) (end: sep n = True):
    List.sumBy (List.splitBy (List.map (List.range 0 n) f) p) (group => g group.toList)
      = Nat.keepIf (g (List.runAt f sep n 0)) (¬(sep 0))
        + List.sumBy (List.range 0 n) (c => Nat.keepIf (g (List.runAt f sep n (Succ c))) (¬(sep (Succ c)) ∧ sep c)) :=
  rewrite List.finishGroupsClose (List.splitGroups (List.map (List.rangeFrom n 0) f) p),
    List.splitGroupsOpen p f sep hsep n 0 end,
    List.closeRunSum g (Pair.snd (List.splitGroups (List.map (List.rangeFrom n 0) f) p)) n 0 f sep,
    List.splitGroupsDone p f sep hsep g n 0 end

--| Whether the positions `lo` to `hi - 1` are a maximal run of positions that aren't separators.
--| That is, the one before it is a separator (or lo is 0), it isn't empty,
--| none in it is a separator, and hi is one.
@[noReceiver]
def Nat.isRun (sep: Nat → Bool) (lo: Nat) (hi: Nat): Bool :=
  (lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (i => ¬(sep i)) ∧ sep hi))

theorem List.isRunNoEdge ∀ (sep: Nat → Bool) (lo: Nat) (hi: Nat) (h: (lo == 0 ∨ sep (lo - 1)) = False): Nat.isRun sep lo hi = False :=
  calc Nat.isRun sep lo hi
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi)))
    _ = False := rewrite h

theorem List.isRunSepStart ∀ (sep: Nat → Bool) (lo: Nat) (hi: Nat) (h: sep lo = True): Nat.isRun sep lo hi = False :=
  calc Nat.isRun sep lo hi
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ (lo < hi ∧ (List.all (List.rangeFrom (hi - lo) lo) (c => ¬(sep c)) ∧ sep hi)))
    _ = ((lo == 0 ∨ sep (lo - 1)) ∧ False) :=
      match e: Nat.leq (Succ lo) hi with
        | False => rfl
        | True => rewrite Nat.subSuccRight lo hi e, h
    _ = False := Bool.andFalse (lo == 0 ∨ sep (lo - 1))

--| A run that starts at lo ends at the first separator after it.
theorem List.isRunEnd ∀ (sep: Nat → Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True) (hi: Nat) (h: Nat.isRun sep lo hi = True):
    hi = Nat.firstFrom sep (Succ (n - lo)) lo :=
  let Both _ (Both long (Both none stop)) := h
  let found := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
    (rewrite Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  match e: Nat.leq hi (Nat.firstFrom sep (Succ (n - lo)) lo) with
    | True => Nat.leAntisym hi (Nat.firstFrom sep (Succ (n - lo)) lo) e (Nat.firstFromLe sep (Succ (n - lo)) lo hi (Nat.lessLe lo hi long) stop)
    | False =>
      Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym found)
        (calc sep (Nat.firstFrom sep (Succ (n - lo)) lo)
          _ = ¬(¬(sep (Nat.firstFrom sep (Succ (n - lo)) lo))) := match sep (Nat.firstFrom sep (Succ (n - lo)) lo) with | True => rfl
          _ = False := rewrite List.allRangeElim (c => ¬(sep c)) (hi - lo) lo none (Nat.firstFrom sep (Succ (n - lo)) lo)
            (Nat.firstFromAtLeast sep (Succ (n - lo)) lo)
            (rewrite Nat.addSubCancel lo hi (Nat.lessLe lo hi long) in e.read))))

--| The run that starts at lo (it does start there) is a maximal run.
theorem List.isRunRun ∀ (sep: Nat → Bool) (n: Nat) (lo: Nat) (hlo: lo < n) (end: sep n = True)
    (h1: sep lo = False) (h2: (lo == 0 ∨ sep (lo - 1)) = True): Nat.isRun sep lo (Nat.firstFrom sep (Succ (n - lo)) lo) = True :=
  let v := Nat.firstFrom sep (Succ (n - lo)) lo
  let found: sep v = True := Nat.firstFromFound sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo)
    (rewrite Nat.addSubCancel lo n (Nat.lessLe lo n hlo) in Nat.leRefl (Succ n)) end
  let atLeast: lo ≤ v := Nat.firstFromAtLeast sep (Succ (n - lo)) lo
  let long: Succ lo ≤ v := Nat.leNeSucc lo v atLeast (e => Bool.falseNotTrue (Eq.trans (Eq.sym h1) (rewrite e in found)))
  Both h2
    (Both long
      (Both (List.allRangeIntro (c => ¬(sep c)) (v - lo) lo (k k1 k2 =>
          rewrite Nat.firstFromBefore sep (Succ (n - lo)) lo k k1 (rewrite <- Nat.addSubCancel lo v atLeast in k2)))
        found))

theorem List.runsFromEdge ∀ (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n) (h1: sep lo = False)
    (b: Bool) (h2: (lo == 0 ∨ sep (lo - 1)) = b): List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
    = Nat.keepIf (g (List.runAt f sep n lo)) b := match b with
      | False => List.sumRangeFromNone (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f)) (Succ n) 0
        (b b1 b2 => List.isRunNoEdge sep lo b h2)
      | True =>
        List.sumRangeFromOne (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f))
          (Nat.firstFrom sep (Succ (n - lo)) lo) (List.isRunRun sep n lo hlo end h1 h2)
          (List.isRunEnd sep n lo hlo end) (Succ n) 0 (Nat.zeroLe (Nat.firstFrom sep (Succ (n - lo)) lo))
          (Nat.firstFromLe sep (Succ (n - lo)) lo n (Nat.lessLe lo n hlo) end)

--| For each lo, the maximal runs starting there: one if a run starts at lo, none otherwise.
theorem List.runsFrom ∀ (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n):
    List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
      = Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))) :=
  List.runsFromStart sep f g n end lo hlo (sep lo) rfl

theorem List.runsFromStart ∀ (sep: Nat → Bool) (f: Nat → a) (g: List a → Nat) (n: Nat) (end: sep n = True) (lo: Nat) (hlo: lo < n)
    (b: Bool) (h1: sep lo = b): List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))
    = Nat.keepIf (g (List.runAt f sep n lo)) (¬b ∧ (lo == 0 ∨ sep (lo - 1))) := match b with
      | True => List.sumRangeFromNone (hi => Nat.isRun sep lo hi) (hi => g (List.map (List.rangeFrom (hi - lo) lo) f)) (Succ n) 0
        (b b1 b2 => List.isRunSepStart sep lo b h1)
      | False => List.runsFromEdge sep f g n end lo hlo h1 (lo == 0 ∨ sep (lo - 1)) rfl

theorem List.sumRangeLast ∀ (f: Nat → Nat) (n: Nat): List.sumBy (List.range 0 (Succ n)) f = List.sumBy (List.range 0 n) f + f n :=
  calc List.sumBy (List.rangeFrom (Succ n) 0) f
    _ = List.sumBy (List.append (List.rangeFrom n 0) (List.rangeFrom 1 (0 + n))) f := rewrite <- List.rangeFromAppend n 1 0 in rfl
    _ = List.sumBy (List.range 0 n) f + f n := List.sumByAppend (List.rangeFrom n 0) (List.rangeFrom 1 n) f

--| The runs by where they start: at 0, or just after a separator.
theorem List.runStarts ∀ (sep: Nat → Bool) (r: Nat → Nat) (n: Nat) (end: sep n = True): List.sumBy (List.range 0 n) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
    = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range 0 n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)) :=
  match n with
    | Zero => rewrite end
    | Succ n =>
      calc List.sumBy (List.rangeFrom (Succ n) 0) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
        _ = Nat.keepIf (r 0) (¬(sep 0) ∧ True)
            + List.sumBy (List.rangeFrom n 1) (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
          := List.sumByCons (List.rangeFrom n 1) 0 (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
        _ = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range 0 n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c))
          := rewrite Bool.andTrue (¬(sep 0)), List.sumByRangeShift (lo => Nat.keepIf (r lo) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1)))) n 0
        _ = Nat.keepIf (r 0) (¬(sep 0)) + (List.sumBy (List.range 0 n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)) + 0)
          := rewrite Nat.addZero (List.sumBy (List.range 0 n) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)))
        _ = Nat.keepIf (r 0) (¬(sep 0)) + List.sumBy (List.range 0 (Succ n)) (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c))
          := rewrite List.sumRangeLast (c => Nat.keepIf (r (Succ c)) (¬(sep (Succ c)) ∧ sep c)) n, end

--| Splitting the positions 0 .. n - 1 at the separators gives exactly the
--| maximal runs `lo .. hi - 1` (`Nat.isRun`), when position n is a separator.
theorem List.splitByRuns ∀ (p: a → Bool) (f: Nat → a) (sep: Nat → Bool) (hsep: ∀ (c: Nat) => p (f c) = sep c) (g: List a → Nat) (n: Nat) (end: sep n = True):
    List.sumBy (List.splitBy (List.map (List.range 0 n) f) p) (group => g group.toList)
      = List.sumBy (List.range 0 n) (lo => List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))) :=
  calc List.sumBy (List.splitBy (List.map (List.range 0 n) f) p) (group => g group.toList)
    _ = Nat.keepIf (g (List.runAt f sep n 0)) (¬(sep 0))
        + List.sumBy (List.range 0 n) (c => Nat.keepIf (g (List.runAt f sep n (Succ c))) (¬(sep (Succ c)) ∧ sep c))
      := List.splitByStarts p f sep hsep g n end
    _ = List.sumBy (List.range 0 n) (lo => Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
      := Eq.sym (List.runStarts sep (lo => g (List.runAt f sep n lo)) n end)
    _ = List.sumBy (List.range 0 n) (lo => List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi)))
      := List.sumByCongRange (lo => Nat.keepIf (g (List.runAt f sep n lo)) (¬(sep lo) ∧ (lo == 0 ∨ sep (lo - 1))))
        (lo => List.sumBy (List.range 0 (Succ n)) (hi => Nat.keepIf (g (List.map (List.rangeFrom (hi - lo) lo) f)) (Nat.isRun sep lo hi))) 0 n
        (lo l1 l2 => Eq.sym (List.runsFrom sep f g n end lo l2))
