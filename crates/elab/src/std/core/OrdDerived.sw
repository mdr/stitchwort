--| The laws `deriving (Ord)` puts together:
--| [`Ordering.thenEqual`], `thenFlip`, `thenTrans`, `tagsTrans`.
-- Loaded with the core: A derived `Ord` instance writes `Ordering.tagsTrans`
-- and its siblings in full (docs/proposals/prelude-slim.md §2.1).

--| Derived orderings compare constructors by position (their tags), then
--| fields left to right with [`Ordering.andThen`]. Their laws are put together
--| from these, proved once. The comparisons are implicit, found from the
--| proofs' types.
-- (docs/proposals/interfaces.md §5.11, stage 7)

--| When `c` then `d` is `Equal`, both are.
theorem Ordering.thenEqual ∀ [c d: Ordering] (h: Ordering.andThen c d = Equal): (c = Equal) ∧ (d = Equal) :=
  Ordering.andThenEqual c d h

--| Comparing the other way round, field by field.
theorem Ordering.thenFlip ∀ [c d c2 d2: Ordering]
    (hc: c2 = Ordering.flip c)
    (hd: d2 = Ordering.flip d):
    Ordering.andThen c2 d2 = Ordering.flip (Ordering.andThen c d) :=
  rewrite hc, hd in Eq.sym (Ordering.flipAndThen c d)

--| `Less` is transitive for a field compared by `cmp`, then the rest.
theorem Ordering.thenTransBy ∀ (cmp: a → a → Ordering) (x y z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (cmp x y) r1 = Less)
    (h2: Ordering.andThen (cmp y z) r2 = Less)
    (t: cmp x y = Less → cmp y z = Less → cmp x z = Less)
    (exy: cmp x y = Equal → x = y)
    (eyz: cmp y z = Equal → y = z)
    (tr: r1 = Less → r2 = Less → r3 = Less):
    Ordering.andThen (cmp x z) r3 = Less :=
  Ordering.andThenTrans
    (cmp x y)
    (cmp y z)
    (cmp x z)
    r1
    r2
    r3
    t
    (e => Eq.cong (w => cmp w z) (exy e))
    (e => Eq.sym (Eq.cong (w => cmp x w) (eyz e)))
    tr
    h1
    h2

--| `Less` is transitive for a field compared by its `Ord` instance, then the rest.
theorem Ord.thenTrans ∀ [auto ord: Ord a] (x y z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (Ord.compare x y) r1 = Less)
    (h2: Ordering.andThen (Ord.compare y z) r2 = Less)
    (tr: r1 = Less → r2 = Less → r3 = Less):
    Ordering.andThen (Ord.compare x z) r3 = Less :=
  Ordering.thenTransBy Ord.compare x y z h1 h2 (ord.trans x y z) (ord.equal x y) (ord.equal y z) tr

--| A derived comparison of two values whose tags are `i` and `j` compares
--| the tags first, and their fields (`f`) only when the tags are equal:
--| `if Nat.equal i j then f else Nat.compare i j`. When that is `Equal`, both
--| the tags and the fields are.
theorem Ordering.tagsEqual ∀ (i j: Nat) (f: Ordering):
    (if Nat.equal i j then f else Nat.compare i j) = Equal → (i = j) ∧ (f = Equal) :=
  match t: Nat.equal i j with
    | True => h => Both (Nat.equalSound i j t) h
    | False => h => Void.exfalso (Nat.equalFalse i j t (Nat.compareEqual i j h))

--| [`Ordering.tagsFlip`] with the tags' tests as variables `b` and `c`.
theorem Ordering.tagsFlipBy ∀ (i j: Nat) (b c: Bool) (f g: Ordering)
    (hb: Nat.equal i j = b)
    (hc: Nat.equal j i = c)
    (e: i = j → g = Ordering.flip f):
    (if c then g else Nat.compare j i) = Ordering.flip (if b then f else Nat.compare i j) :=
  match b, c with
    | True, True => e (Nat.equalSound i j hb)
    | True, False => Void.exfalso (Nat.equalFalse j i hc (Eq.sym (Nat.equalSound i j hb)))
    | False, True => Void.exfalso (Nat.equalFalse i j hb (Eq.sym (Nat.equalSound j i hc)))
    | False, False => Nat.compareFlip i j

--| Comparing the other way round, tags first: the fields' comparisons `f`
--| and `g` need only flip when the tags are equal.
theorem Ordering.tagsFlip ∀ (i j: Nat) (f g: Ordering)
    (e: i = j → g = Ordering.flip f):
    (if Nat.equal j i then g else Nat.compare j i) = Ordering.flip (if Nat.equal i j then f else Nat.compare i j) :=
  Ordering.tagsFlipBy i j (Nat.equal i j) (Nat.equal j i) f g rfl rfl e

--| [`Ordering.tagsTrans`] with the tags' tests as variables `b`, `c` and `d`.
theorem Ordering.tagsTransBy ∀ (i j k: Nat) (b c d: Bool) (f g h: Ordering)
    (hb: Nat.equal i j = b)
    (hc: Nat.equal j k = c)
    (hd: Nat.equal i k = d)
    (tr: i = j → j = k → f = Less → g = Less → h = Less)
    (h1: (if b then f else Nat.compare i j) = Less)
    (h2: (if c then g else Nat.compare j k) = Less):
    (if d then h else Nat.compare i k) = Less :=
  match b, c, d with
    | True, True, True => tr (Nat.equalSound i j hb) (Nat.equalSound j k hc) h1 h2
    | True, True, False =>
      Void.exfalso (Nat.equalFalse i k hd (Eq.trans (Nat.equalSound i j hb) (Nat.equalSound j k hc)))
    | True, False, True =>
      Void.exfalso (Nat.equalFalse j k hc (Eq.trans (Eq.sym (Nat.equalSound i j hb)) (Nat.equalSound i k hd)))
    | True, False, False => rewrite Nat.equalSound i j hb in h2
    | False, True, True =>
      Void.exfalso (Nat.equalFalse i j hb (Eq.trans (Nat.equalSound i k hd) (Eq.sym (Nat.equalSound j k hc))))
    | False, True, False => rewrite Eq.sym (Nat.equalSound j k hc) in h1
    | False, False, True =>
      let less: Nat.compare i k = Less := Nat.compareTrans i j k h1 h2
      let equal: Nat.compare i k = Equal :=
        Eq.trans (Eq.cong (x => Nat.compare i x) (Eq.sym (Nat.equalSound i k hd))) (Nat.compareSelf i)
      Void.exfalso (Ordering.equalNotLess (Eq.trans (Eq.sym equal) less))
    | False, False, False => Nat.compareTrans i j k h1 h2

--| `Less` is transitive for comparisons that compare tags first: the fields'
--| comparisons `f`, `g` and `h` need only be transitive when all three tags
--| are equal.
theorem Ordering.tagsTrans ∀ (i j k: Nat) (f g h: Ordering)
    (tr: i = j → j = k → f = Less → g = Less → h = Less)
    (h1: (if Nat.equal i j then f else Nat.compare i j) = Less)
    (h2: (if Nat.equal j k then g else Nat.compare j k) = Less):
    (if Nat.equal i k then h else Nat.compare i k) = Less :=
  Ordering.tagsTransBy i j k (Nat.equal i j) (Nat.equal j k) (Nat.equal i k) f g h rfl rfl rfl tr h1 h2
