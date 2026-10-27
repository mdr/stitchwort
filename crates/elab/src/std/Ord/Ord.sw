-- Helpers over `Ord`: ordering by a key, `max` and `min`, and the order
-- lemmas `leTrans`, `lessLe` and `lessTrans`. The helpers were in the
-- core (docs/proposals/prelude-slim.md stage 3); no instance needs them.

-- A comparison that's its own opposite is `Equal`.
theorem Ordering.flipSelf: (c: Ordering) → c = Ordering.flip c → c = Equal
  | Less, h => Void.exfalso (Ordering.lessNotGreater h)
  | Equal, h => rfl
  | Greater, h => Void.exfalso (Ordering.greaterNotLess h)

-- Orders `a` by a key, given that the key tells values apart. The relations
-- are the key's own, applied to the keys, so `x < y` is `key x < key y`
-- and reduces the way the key's does (D414).
def Ord.byKey [auto decEq: DecEq a] [auto ord: Ord b] (key: a → b)
    (inj: (x: a) → (y: a) → key x = key y → x = y): Ord a := {
  compare = x y => Ord.compare (key x) (key y),
  lessThan = x y => ord.lessThan (key x) (key y),
  lessEq = x y => ord.lessEq (key x) (key y),
  decLessThan = x y => ord.decLessThan (key x) (key y),
  decLessEq = x y => ord.decLessEq (key x) (key y),
  equal = x y h => inj x y (ord.equal (key x) (key y) h),
  flip = x y => ord.flip (key x) (key y),
  trans = x y z => ord.trans (key x) (key y) (key z),
  lessThanOf = x y h => ord.lessThanOf (key x) (key y) h,
  lessThanTo = x y h => ord.lessThanTo (key x) (key y) h,
  lessEqOf = x y h => ord.lessEqOf (key x) (key y) h,
  lessEqTo = x y h => ord.lessEqTo (key x) (key y) h
}

-- The opposite order, largest first (Haskell's `Down`, Rust's `Reverse`):
-- `List.sort [ord := Ord.reverse] xs` sorts in descending order.
def Ord.reverse [auto ord: Ord a]: Ord a :=
  Ord.fromCompare [decEq := ord.eq] (x y => Ord.compare y x)
    (x y h => Eq.sym (ord.equal y x h))
    (x y => ord.flip y x)
    (x y z h1 h2 => ord.trans z y x h2 h1)

-- The larger, and the smaller (the first, if they're equal).
def Ord.max [auto ord: Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Less => y
  | _ => x

def Ord.min [auto ord: Ord a] (x: a) (y: a): a := match Ord.compare x y with
  | Greater => y
  | _ => x

-- Anything compares `Equal` with itself.
theorem Ord.compareSelf [auto ord: Ord a] (x: a): Ord.compare x x = Equal :=
  Ordering.flipSelf (Ord.compare x x) (ord.flip x x)

-- `c3` isn't `Greater` when `c1` and `c2` aren't, given what `Ord`'s laws
-- say of three comparisons `x y`, `y z` and `x z`: `Less` is transitive,
-- and an `Equal` makes two of them the same.
theorem Ordering.notGreaterTrans: (c1: Ordering) → (c2: Ordering) → (c3: Ordering) →
    (c1 = Less → c2 = Less → c3 = Less) → (c1 = Equal → c3 = c2) → (c2 = Equal → c3 = c1) →
    Not (c1 = Greater) → Not (c2 = Greater) → Not (c3 = Greater)
  | Less, Less, c3, t, e1, e2, n1, n2, g => Ordering.lessNotGreater (Eq.trans (Eq.sym (t rfl rfl)) g)
  | Less, Equal, c3, t, e1, e2, n1, n2, g => Ordering.lessNotGreater (Eq.trans (Eq.sym (e2 rfl)) g)
  | Less, Greater, c3, t, e1, e2, n1, n2, g => n2 rfl
  | Equal, c2, c3, t, e1, e2, n1, n2, g => n2 (Eq.trans (Eq.sym (e1 rfl)) g)
  | Greater, c2, c3, t, e1, e2, n1, n2, g => n1 rfl

-- `<=` and `<` are transitive, and `<` is `<=`, for any `Ord`.
theorem Ord.leTrans [auto ord: Ord a] (x: a) (y: a) (z: a) (h1: x <= y) (h2: y <= z): x <= z :=
  ord.lessEqOf x z
    (Ordering.notGreaterTrans (Ord.compare x y) (Ord.compare y z) (Ord.compare x z) (ord.trans x y z)
      (e => Eq.cong (w => Ord.compare w z) (ord.equal x y e))
      (e => Eq.sym (Eq.cong (w => Ord.compare x w) (ord.equal y z e)))
      (ord.lessEqTo x y h1) (ord.lessEqTo y z h2))

theorem Ord.lessLe [auto ord: Ord a] (x: a) (y: a) (h: x < y): x <= y :=
  ord.lessEqOf x y (g => Ordering.lessNotGreater (Eq.trans (Eq.sym (ord.lessThanTo x y h)) g))

theorem Ord.lessTrans [auto ord: Ord a] (x: a) (y: a) (z: a) (h1: x < y) (h2: y < z): x < z :=
  ord.lessThanOf x z (ord.trans x y z (ord.lessThanTo x y h1) (ord.lessThanTo y z h2))
