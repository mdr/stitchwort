-- Helpers over `Ord`: ordering by a key, `max` and `min`. These were in the
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
