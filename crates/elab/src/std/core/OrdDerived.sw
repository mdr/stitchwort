-- core/OrdDerived.sw. The laws `deriving (Ord)` puts together:
-- `Ordering.thenEqual`, `thenFlip`, `thenTrans`, `byTagTrans`. Loaded with
-- the core: A derived `Ord` instance writes `Ordering.byTagTrans` and its
-- siblings in full (docs/proposals/prelude-slim.md §2.1).

-- Derived orderings (docs/proposals/interfaces.md §5.11, stage 7) compare
-- constructors by position (their tags), then fields left to right with
-- `Ordering.andThen`. Their laws are put together from these, proved once.
-- The comparisons are implicit, found from the proofs' types.

-- Both are `Equal` when `c` then `d` is.
theorem Ordering.thenEqual [c d: Ordering] (h: Ordering.andThen c d = Equal): And (c = Equal) (d = Equal) :=
  Ordering.andThenEqual c d h

-- Comparing the other way round, field by field.
theorem Ordering.thenFlip [c d c2 d2: Ordering] (hc: c2 = Ordering.flip c) (hd: d2 = Ordering.flip d):
    Ordering.andThen c2 d2 = Ordering.flip (Ordering.andThen c d) :=
  rewrite hc, hd in Eq.sym (Ordering.flipAndThen c d)

-- `Less` is transitive for a field compared by `cmp`, then the rest.
theorem Ordering.thenTransBy (cmp: a -> a -> Ordering) (x: a) (y: a) (z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (cmp x y) r1 = Less) (h2: Ordering.andThen (cmp y z) r2 = Less)
    (t: cmp x y = Less -> cmp y z = Less -> cmp x z = Less)
    (exy: cmp x y = Equal -> x = y) (eyz: cmp y z = Equal -> y = z)
    (tr: r1 = Less -> r2 = Less -> r3 = Less):
    Ordering.andThen (cmp x z) r3 = Less :=
  Ordering.andThenTrans (cmp x y) (cmp y z) (cmp x z) r1 r2 r3 t
    (e => Eq.cong (w => cmp w z) (exy e))
    (e => Eq.sym (Eq.cong (w => cmp x w) (eyz e)))
    tr h1 h2

-- The same for a field compared by its `Ord` instance.
theorem Ord.thenTrans [auto ord: Ord a] (x: a) (y: a) (z: a) [r1 r2 r3: Ordering]
    (h1: Ordering.andThen (Ord.compare x y) r1 = Less) (h2: Ordering.andThen (Ord.compare y z) r2 = Less)
    (tr: r1 = Less -> r2 = Less -> r3 = Less):
    Ordering.andThen (Ord.compare x z) r3 = Less :=
  Ordering.thenTransBy Ord.compare x y z h1 h2 (ord.trans x y z) (ord.equal x y) (ord.equal y z) tr

-- Whether both comparisons are `Equal`.
def Ordering.bothEqual: Ordering -> Ordering -> Bool
  | Equal, Equal => True
  | _,     _     => False

theorem Ordering.notBothEqual: (c: Ordering) -> (d: Ordering) -> Ordering.bothEqual c d = False -> c = Equal -> d = Equal -> Void
  | Equal,   Equal,   t, e1, e2 => Bool.trueNotFalse t
  | Equal,   Less,    t, e1, e2 => Ordering.lessNotEqual e2
  | Equal,   Greater, t, e1, e2 => Ordering.greaterNotEqual e2
  | Less,    d,       t, e1, e2 => Ordering.lessNotEqual e1
  | Greater, d,       t, e1, e2 => Ordering.greaterNotEqual e1

-- As `Ordering.andThenTrans`, where the rest need only be transitive when
-- both first comparisons are `Equal`.
theorem Ordering.andThenTransWhen: (c1: Ordering) -> (c2: Ordering) -> (c3: Ordering) ->
    (r1: Ordering) -> (r2: Ordering) -> (r3: Ordering) ->
    (c1 = Less -> c2 = Less -> c3 = Less) -> (c1 = Equal -> c3 = c2) -> (c2 = Equal -> c3 = c1) ->
    (c1 = Equal -> c2 = Equal -> r1 = Less -> r2 = Less -> r3 = Less) ->
    Ordering.andThen c1 r1 = Less -> Ordering.andThen c2 r2 = Less -> Ordering.andThen c3 r3 = Less
  | Less,    Less,    c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite t rfl rfl in rfl
  | Less,    Equal,   c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e2 rfl in rfl
  | Less,    Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Equal,   Less,    c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in rfl
  | Equal,   Equal,   c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => rewrite e1 rfl in tr rfl rfl h1 h2
  | Equal,   Greater, c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Greater, c2,      c3, r1, r2, r3, t, e1, e2, tr, h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)

-- Transitivity with the tags compared first. A derived `trans` uses it for
-- values not all of one constructor, where `tr` is never needed: the tags
-- can't all be equal. (The rest are explicit here: where the tags are
-- numbers, the comparisons compute without them.)
theorem Ordering.byTagTrans (i: Nat) (j: Nat) (k: Nat) (r1: Ordering) (r2: Ordering) (r3: Ordering)
    (h1: Ordering.andThen (Nat.compare i j) r1 = Less) (h2: Ordering.andThen (Nat.compare j k) r2 = Less)
    (tr: Nat.compare i j = Equal -> Nat.compare j k = Equal -> r1 = Less -> r2 = Less -> r3 = Less):
    Ordering.andThen (Nat.compare i k) r3 = Less :=
  Ordering.andThenTransWhen (Nat.compare i j) (Nat.compare j k) (Nat.compare i k) r1 r2 r3
    (Nat.compareTrans i j k)
    (e => Eq.cong (w => Nat.compare w k) (Nat.compareEqual i j e))
    (e => Eq.sym (Eq.cong (w => Nat.compare i w) (Nat.compareEqual j k e)))
    tr h1 h2

