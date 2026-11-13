--| The laws `deriving (Ord)` puts together:
--| [`Ordering.thenEqual`], `thenFlip`, `thenTrans`, `byTagTrans`.
-- Loaded with the core: A derived `Ord` instance writes `Ordering.byTagTrans`
-- and its siblings in full (docs/proposals/prelude-slim.md §2.1).

--| Derived orderings compare constructors by position (their tags), then
--| fields left to right with [`Ordering.andThen`]. Their laws are put together
--| from these, proved once. The comparisons are implicit, found from the
--| proofs' types.
-- (docs/proposals/interfaces.md §5.11, stage 7)

--| When `c` then `d` is `Equal`, both are.
theorem Ordering.thenEqual [c d: Ordering] (h: Ordering.andThen c d = Equal): (c = Equal) ∧ (d = Equal) :=
  Ordering.andThenEqual c d h

--| Comparing the other way round, field by field.
theorem Ordering.thenFlip [c d c2 d2: Ordering] (hc: c2 = Ordering.flip c) (hd: d2 = Ordering.flip d):
    Ordering.andThen c2 d2 = Ordering.flip (Ordering.andThen c d) :=
  rewrite hc, hd in Eq.sym (Ordering.flipAndThen c d)

--| `Less` is transitive for a field compared by `cmp`, then the rest.
theorem Ordering.thenTransBy (cmp: a → a → Ordering) (x: a) (y: a) (z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (cmp x y) r1 = Less) (h2: Ordering.andThen (cmp y z) r2 = Less)
    (t: cmp x y = Less → cmp y z = Less → cmp x z = Less)
    (exy: cmp x y = Equal → x = y) (eyz: cmp y z = Equal → y = z)
    (tr: r1 = Less → r2 = Less → r3 = Less):
    Ordering.andThen (cmp x z) r3 = Less :=
  Ordering.andThenTrans (cmp x y) (cmp y z) (cmp x z) r1 r2 r3 t
    (e => Eq.cong (w => cmp w z) (exy e))
    (e => Eq.sym (Eq.cong (w => cmp x w) (eyz e)))
    tr h1 h2

--| `Less` is transitive for a field compared by its `Ord` instance, then the rest.
theorem Ord.thenTrans [auto ord: Ord a] (x: a) (y: a) (z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (Ord.compare x y) r1 = Less) (h2: Ordering.andThen (Ord.compare y z) r2 = Less)
    (tr: r1 = Less → r2 = Less → r3 = Less):
    Ordering.andThen (Ord.compare x z) r3 = Less :=
  Ordering.thenTransBy Ord.compare x y z h1 h2 (ord.trans x y z) (ord.equal x y) (ord.equal y z) tr

--| Whether both comparisons are `Equal`.
def Ordering.bothEqual: (x: Ordering) → (y: Ordering) → Bool := matches | Equal, Equal

theorem Ordering.notBothEqual (c d: Ordering) (t: Ordering.bothEqual c d = False) (e1: c = Equal) (e2: d = Equal): Void :=
  match c, d with
    | Equal, Equal => Bool.trueNotFalse t

--| As [`Ordering.andThenTrans`], where the rest need only be transitive when
--| both first comparisons are `Equal`.
theorem Ordering.andThenTransWhen (c1 c2 c3 r1 r2 r3: Ordering)
    (t: c1 = Less → c2 = Less → c3 = Less) (e1: c1 = Equal → c3 = c2) (e2: c2 = Equal → c3 = c1)
    (tr: c1 = Equal → c2 = Equal → r1 = Less → r2 = Less → r3 = Less)
    (h1: Ordering.andThen c1 r1 = Less) (h2: Ordering.andThen c2 r2 = Less): Ordering.andThen c3 r3 = Less :=
  match c1, c2 with
    | Less, Less => rewrite t rfl rfl in rfl
    | Less, Equal => rewrite e2 rfl in rfl
    | Equal, Less => rewrite e1 rfl in rfl
    | Equal, Equal => rewrite e1 rfl in tr rfl rfl h1 h2

--| Transitivity with the tags compared first. A derived `trans` uses it for
--| values not all of one constructor, where `tr` is never needed: the tags
--| can't all be equal.
-- (The rest are explicit here: where the tags are numbers, the comparisons
-- compute without them.)
theorem Ordering.byTagTrans (i: Nat) (j: Nat) (k: Nat) (r1: Ordering) (r2: Ordering) (r3: Ordering)
    (h1: Ordering.andThen (Nat.compare i j) r1 = Less) (h2: Ordering.andThen (Nat.compare j k) r2 = Less)
    (tr: Nat.compare i j = Equal → Nat.compare j k = Equal → r1 = Less → r2 = Less → r3 = Less):
    Ordering.andThen (Nat.compare i k) r3 = Less :=
  Ordering.andThenTransWhen (Nat.compare i j) (Nat.compare j k) (Nat.compare i k) r1 r2 r3
    (Nat.compareTrans i j k)
    (e => Eq.cong (w => Nat.compare w k) (Nat.compareEqual i j e))
    (e => Eq.sym (Eq.cong (w => Nat.compare i w) (Nat.compareEqual j k e)))
    tr h1 h2
