-- core/Ord.sw. The `Ord` interface, `Ord.fromCompare`, and the `Ord`
-- instances for the core types. Loaded with the core: `< <=` and `deriving
-- (Ord)` go through `Ord` dictionaries, found by full key
-- (docs/proposals/prelude-slim.md §2.1).

theorem Bool.toNatInjective: (a: Bool) -> (b: Bool) -> Bool.toNat a = Bool.toNat b -> a = b
  | False, False, h => rfl
  | False, True,  h => Void.exfalso (Nat.zeroNotSucc 0 h)
  | True,  False, h => Void.exfalso (Nat.succNotZero 0 h)
  | True,  True,  h => rfl

-- `False` first.
def Bool.compare (a: Bool) (b: Bool): Ordering := Nat.compare (Bool.toNat a) (Bool.toNat b)

-- `Less`, `Equal`, `Greater`.
def Ordering.compare (c: Ordering) (d: Ordering): Ordering := Nat.compare (Ordering.index c) (Ordering.index d)

-- A total order: a comparison with its laws, and the relations `<` and `<=`
-- with their decisions, agreeing with it (docs/proposals/interfaces.md
-- §6.2, D180; the fields are `lessThan` and `lessEq`, D200). The relations
-- are fields so that `Nat`'s can be `Nat.LessThan` and `Nat.LessEq`
-- themselves. Build one with `Ord.fromCompare` or `Ord.byKey`.
interface Ord (a: Type) =
  { eq: DecEq a
  , compare: a -> a -> Ordering
  , lessThan: a -> a -> Prop
  , lessEq: a -> a -> Prop
  , decLessThan: (x: a) -> (y: a) -> Decidable (lessThan x y)
  , decLessEq: (x: a) -> (y: a) -> Decidable (lessEq x y)
  -- `Equal` means equal; the other way round is the opposite; `Less` is
  -- transitive.
  , equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y
  , flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y)
  , trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less
  -- The relations agree with `compare`.
  , lessThanOf: (x: a) -> (y: a) -> compare x y = Less -> lessThan x y
  , lessThanTo: (x: a) -> (y: a) -> lessThan x y -> compare x y = Less
  , lessEqOf: (x: a) -> (y: a) -> Not (compare x y = Greater) -> lessEq x y
  , lessEqTo: (x: a) -> (y: a) -> lessEq x y -> Not (compare x y = Greater)
  }

-- From a comparison and its three laws. The relations are
-- `compare x y = Less` and `Not (compare x y = Greater)`, decided through
-- `DecEq Ordering`. `eq` is the `decEq` given.
def Ord.fromCompare [auto decEq: DecEq a] (compare: a -> a -> Ordering)
    (equal: (x: a) -> (y: a) -> compare x y = Equal -> x = y)
    (flip: (x: a) -> (y: a) -> compare y x = Ordering.flip (compare x y))
    (trans: (x: a) -> (y: a) -> (z: a) -> compare x y = Less -> compare y z = Less -> compare x z = Less): Ord a :=
  { compare = compare
  , lessThan = x y => compare x y = Less
  , lessEq = x y => Not (compare x y = Greater)
  , decLessThan = x y => Ordering.decEq (compare x y) Less
  , decLessEq = x y => Decidable.not (Ordering.decEq (compare x y) Greater)
  , equal = equal
  , flip = flip
  , trans = trans
  , lessThanOf = x y h => h
  , lessThanTo = x y h => h
  , lessEqOf = x y h => h
  , lessEqTo = x y h => h
  }

instance Nat.instOrd: Ord Nat :=
  { compare = Nat.compare
  , lessThan = Nat.LessThan
  , lessEq = Nat.LessEq
  , decLessThan = Nat.decLessThan
  , decLessEq = Nat.decLessEq
  , equal = Nat.compareEqual
  , flip = Nat.compareFlip
  , trans = Nat.compareTrans
  , lessThanOf = Nat.lessOfCompare
  , lessThanTo = Nat.compareOfLess
  , lessEqOf = Nat.leOfCompare
  , lessEqTo = Nat.compareOfLe
  }

instance Int.instOrd: Ord Int :=
  { compare = Int.compare
  , lessThan = Int.LessThan
  , lessEq = Int.LessEq
  , decLessThan = Int.decLessThan
  , decLessEq = Int.decLessEq
  , equal = Int.compareEqual
  , flip = Int.compareFlip
  , trans = Int.compareTrans
  , lessThanOf = Int.lessOfCompare
  , lessThanTo = Int.compareOfLess
  , lessEqOf = Int.leOfCompare
  , lessEqTo = Int.compareOfLe
  }

instance Char.instOrd: Ord Char :=
  Ord.fromCompare Char.compare Char.compareEqual Char.compareFlip Char.compareTrans

instance Text.instOrd: Ord Text :=
  Ord.fromCompare Text.compare Text.compareEqual Text.compareFlip Text.compareTrans

instance Bool.instOrd: Ord Bool :=
  Ord.fromCompare Bool.compare
    (x y h => Bool.toNatInjective x y (Nat.compareEqual (Bool.toNat x) (Bool.toNat y) h))
    (x y => Nat.compareFlip (Bool.toNat x) (Bool.toNat y))
    (x y z => Nat.compareTrans (Bool.toNat x) (Bool.toNat y) (Bool.toNat z))

instance Ordering.instOrd: Ord Ordering :=
  Ord.fromCompare Ordering.compare
    (x y h => Ordering.indexInjective x y (Nat.compareEqual (Ordering.index x) (Ordering.index y) h))
    (x y => Nat.compareFlip (Ordering.index x) (Ordering.index y))
    (x y z => Nat.compareTrans (Ordering.index x) (Ordering.index y) (Ordering.index z))

instance List.instOrd [auto ord: Ord a]: Ord (List a) :=
  Ord.fromCompare (List.compareLex Ord.compare)
    (List.compareLexEqual Ord.compare ord.equal)
    (List.compareLexFlip Ord.compare ord.flip)
    (List.compareLexTrans Ord.compare ord.equal ord.trans)

instance Option.instOrd [auto ord: Ord a]: Ord (Option a) :=
  Ord.fromCompare (Option.compareWith Ord.compare)
    (Option.compareWithEqual Ord.compare ord.equal)
    (Option.compareWithFlip Ord.compare ord.flip)
    (Option.compareWithTrans Ord.compare ord.trans)

instance Pair.instOrd [auto ordA: Ord a] [auto ordB: Ord b]: Ord (Pair a b) :=
  Ord.fromCompare (Pair.compareWith Ord.compare Ord.compare)
    (Pair.compareWithEqual Ord.compare Ord.compare ordA.equal ordB.equal)
    (Pair.compareWithFlip Ord.compare Ord.compare ordA.flip ordB.flip)
    (Pair.compareWithTrans Ord.compare Ord.compare ordA.equal ordA.trans ordB.trans)

