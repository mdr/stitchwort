-- List lemmas the proofs share: a `drop` read by index, sums over lists
-- zipped in step as sums over indices, and sums over a range that is longer
-- than needed or starts later.

namespace Aoc.Year2024.Day04.Proofs
import Std (And, Bool, Char, DecEq, Decidable, Eq, List, Nat, Option, Void)

-- Index j after dropping k is index k + j before.
theorem getDrop: (xs: List a) → (k: Nat) → (j: Nat) → List.get (List.drop xs k) j = List.get xs (k + j)
  | xs, Zero, j => rfl
  | Nil, Succ k, j => rfl
  | Cons x xs, Succ k, j => getDrop xs k j

theorem decSomeToBool (x: a) (y: a): (d: Decidable (x = y)) → Decidable.toBool (Option.decSome x y d) = Decidable.toBool d
  | Yes p => rfl
  | No r => rfl

-- Optional letters are equal when the letters are.
theorem someEq (x: Char) (y: Char): (Some x == Some y) = (x == y) := decSomeToBool x y (Char.decEq x y)

-- `f` of four elements when all four are there, otherwise 0.
def at4 (f: a → b → c → d → Nat): Option a → Option b → Option c → Option d → Nat
  | Some x, Some y, Some z, Some w => f x y z w
  | _, _, _, _ => 0

-- The same for three.
def at3 (f: a → b → c → Nat): Option a → Option b → Option c → Nat
  | Some x, Some y, Some z => f x y z
  | _, _, _ => 0

-- A sum of zeros.
theorem sumRangeZero (f: Nat → Nat) (n: Nat) (zero: (j: Nat) → f j = 0): List.sumBy (List.range n) f = 0 :=
  List.sumByZeroIntro (List.range n) f (j _ => zero j)

-- Four optional elements with one missing.
theorem at4None2 (f: a → b → c → d → Nat) (y: Option c) (z: Option d): (x: Option a) → at4 f x None y z = 0
  | None => rfl
  | Some x => rfl

theorem at4None3 (f: a → b → c → d → Nat) (z: Option d): (x: Option a) → (y: Option b) → at4 f x y None z = 0
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

theorem at4None4 (f: a → b → c → d → Nat): (x: Option a) → (y: Option b) → (z: Option c) → at4 f x y z None = 0
  | None, y, z => rfl
  | Some x, None, z => rfl
  | Some x, Some y, None => rfl
  | Some x, Some y, Some z => rfl

-- A sum over four lists zipped in step is a sum over the indices, up to any
-- bound at least as long as the first list.
theorem sumByZipWith4 (g: e → Nat) (f: a → b → c → d → e):
    (as: List a) → (bs: List b) → (cs: List c) → (ds: List d) → (n: Nat) → List.length as ≤ n →
    List.sumBy (List.zipWith4 as bs cs ds f) g
      = List.sumBy (List.range n) (j => at4 (x y z w => g (f x y z w)) (List.get as j) (List.get bs j) (List.get cs j) (List.get ds j))
  | Nil, bs, cs, ds, n, h => Eq.sym (sumRangeZero _ n (j => rfl))
  | Cons x xs, Nil, cs, ds, n, h => Eq.sym (sumRangeZero _ n (j => at4None2 _ _ _ _))
  | Cons x xs, Cons y ys, Nil, ds, n, h => Eq.sym (sumRangeZero _ n (j => at4None3 _ _ _ _))
  | Cons x xs, Cons y ys, Cons z zs, Nil, n, h => Eq.sym (sumRangeZero _ n (j => at4None4 _ _ _ _))
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws, Succ n, h =>
    let each := (j: Nat) => at4 (x y z w => g (f x y z w)) (List.get (Cons x xs) j) (List.get (Cons y ys) j) (List.get (Cons z zs) j) (List.get (Cons w ws) j)
    calc List.sumBy (Cons (f x y z w) (List.zipWith4 xs ys zs ws f)) g
      _ = g (f x y z w) + List.sumBy (List.zipWith4 xs ys zs ws f) g := List.sumByCons (List.zipWith4 xs ys zs ws f) (f x y z w) g
      _ = each 0 + List.sumBy (List.range n) (j => each (Succ j)) := rewrite sumByZipWith4 g f xs ys zs ws n h
      _ = List.sumBy (List.range (Succ n)) each := Eq.sym (List.sumByRangeSucc each n)

theorem at3None2 (f: a → b → c → Nat) (z: Option c): (x: Option a) → at3 f x None z = 0
  | None => rfl
  | Some x => rfl

theorem at3None3 (f: a → b → c → Nat): (x: Option a) → (y: Option b) → at3 f x y None = 0
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

-- The same for three lists.
theorem sumByZipWith3 (g: d → Nat) (f: a → b → c → d):
    (as: List a) → (bs: List b) → (cs: List c) → (n: Nat) → List.length as ≤ n →
    List.sumBy (List.zipWith3 as bs cs f) g = List.sumBy (List.range n) (j => at3 (x y z => g (f x y z)) (List.get as j) (List.get bs j) (List.get cs j))
  | Nil, bs, cs, n, h => Eq.sym (sumRangeZero _ n (j => rfl))
  | Cons x xs, Nil, cs, n, h => Eq.sym (sumRangeZero _ n (j => at3None2 _ _ _))
  | Cons x xs, Cons y ys, Nil, n, h => Eq.sym (sumRangeZero _ n (j => at3None3 _ _ _))
  | Cons x xs, Cons y ys, Cons z zs, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Cons y ys, Cons z zs, Succ n, h =>
    let each := (j: Nat) => at3 (x y z => g (f x y z)) (List.get (Cons x xs) j) (List.get (Cons y ys) j) (List.get (Cons z zs) j)
    calc List.sumBy (Cons (f x y z) (List.zipWith3 xs ys zs f)) g
      _ = g (f x y z) + List.sumBy (List.zipWith3 xs ys zs f) g := List.sumByCons (List.zipWith3 xs ys zs f) (f x y z) g
      _ = each 0 + List.sumBy (List.range n) (j => each (Succ j)) := rewrite sumByZipWith3 g f xs ys zs n h
      _ = List.sumBy (List.range (Succ n)) each := Eq.sym (List.sumByRangeSucc each n)

-- A sum over a range is the same over a longer one when the terms past the
-- shorter are 0.
theorem sumRangeExtend (f: Nat → Nat) (n: Nat) (m: Nat) (le: n ≤ m) (zero: (j: Nat) → n ≤ j → f j = 0):
    List.sumBy (List.range m) f = List.sumBy (List.range n) f :=
  let rest := List.sumByZeroIntro (List.rangeFrom (m - n) n) f (j mem => zero j (List.memRangeFrom j (m - n) n mem).left)
  calc List.sumBy (List.range m) f
    _ = List.sumBy (List.range n) f + List.sumBy (List.rangeFrom (m - n) n) f := List.sumByRangeSplit f n m le
    _ = List.sumBy (List.range n) f := rewrite rest in omega

-- A sum over n + k indices whose first k terms are 0 is the sum of the rest,
-- counted from 0.
theorem sumShift (k: Nat) (f: Nat → Nat) (g: Nat → Nat) (n: Nat) (early: (i: Nat) → i < k → f i = 0) (later: (i: Nat) → f (k + i) = g i):
    List.sumBy (List.range (n + k)) f = List.sumBy (List.range n) g :=
  let first := List.sumByZeroIntro (List.range k) f (i mem => early i (List.memRangeFrom i k 0 mem).right)
  let back: n + k - k = n := omega
  calc List.sumBy (List.range (n + k)) f
    _ = List.sumBy (List.range k) f + List.sumBy (List.rangeFrom (n + k - k) k) f := List.sumByRangeSplit f k (n + k) omega
    _ = List.sumBy (List.rangeFrom n k) f := rewrite first, back in rfl
    _ = List.sumBy (List.range n) (i => f (k + i)) := List.sumByRangeOffset f k n
    _ = List.sumBy (List.range n) g := rewrite later _

-- A double sum of two terms is two double sums.
theorem sumBy2Add (n: Nat) (m: Nat) (f: Nat → Nat → Nat) (g: Nat → Nat → Nat):
    List.sumBy (List.range n) (r => List.sumBy (List.range m) (c => f r c + g r c))
      = List.sumBy (List.range n) (r => List.sumBy (List.range m) (c => f r c)) + List.sumBy (List.range n) (r => List.sumBy (List.range m) (c => g r c)) :=
  Eq.trans
    (List.sumByCong (List.range n) _ _ (r => List.sumByAdd (List.range m) (c => f r c) (c => g r c)))
    (List.sumByAdd (List.range n) (r => List.sumBy (List.range m) (c => f r c)) (r => List.sumBy (List.range m) (c => g r c)))

-- A sum is a `sumBy` of each element itself.
theorem sumIsSumBy (xs: List Nat): List.sum xs = List.sumBy xs (x => x) := rfl

-- Four lists zipped in step, with one empty.
theorem zipWith4Nil2 (cs: List c) (ds: List d) (f: a → b → c → d → e): (as: List a) → List.zipWith4 as Nil cs ds f = Nil
  | Nil => rfl
  | Cons x xs => rfl

theorem zipWith4Nil3 (ds: List d) (f: a → b → c → d → e): (as: List a) → (bs: List b) → List.zipWith4 as bs Nil ds f = Nil
  | Nil, bs => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys => rfl

theorem zipWith4Nil4 (f: a → b → c → d → e): (as: List a) → (bs: List b) → (cs: List c) → List.zipWith4 as bs cs Nil f = Nil
  | Nil, bs, cs => rfl
  | Cons x xs, Nil, cs => rfl
  | Cons x xs, Cons y ys, Nil => rfl
  | Cons x xs, Cons y ys, Cons z zs => rfl

-- `at4` of optional elements is `f` of them with defaults for the missing
-- ones, when a default anywhere makes `f` 0.
theorem at4OrElse (f: a → b → c → d → Nat) (da: a) (db: b) (dc: c) (dd: d)
    (zero1: (y: b) → (z: c) → (w: d) → f da y z w = 0)
    (zero2: (x: a) → (z: c) → (w: d) → f x db z w = 0)
    (zero3: (x: a) → (y: b) → (w: d) → f x y dc w = 0)
    (zero4: (x: a) → (y: b) → (z: c) → f x y z dd = 0):
    (oa: Option a) → (ob: Option b) → (oc: Option c) → (od: Option d) →
    at4 f oa ob oc od = f (Option.getOrElse oa da) (Option.getOrElse ob db) (Option.getOrElse oc dc) (Option.getOrElse od dd)
  | None, ob, oc, od => Eq.sym (zero1 _ _ _)
  | Some x, None, oc, od => Eq.sym (zero2 _ _ _)
  | Some x, Some y, None, od => Eq.sym (zero3 _ _ _)
  | Some x, Some y, Some z, None => Eq.sym (zero4 _ _ _)
  | Some x, Some y, Some z, Some w => rfl

-- `f` of three elements when all three are there.
def some3 (f: a → b → c → d): Option a → Option b → Option c → Option d
  | Some x, Some y, Some z => Some (f x y z)
  | _, _, _ => None

theorem some3None2 (f: a → b → c → d) (z: Option c): (x: Option a) → some3 f x None z = None
  | None => rfl
  | Some x => rfl

theorem some3None3 (f: a → b → c → d): (x: Option a) → (y: Option b) → some3 f x y None = None
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

-- Index j of three lists zipped in step.
theorem getZipWith3 (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → (j: Nat) →
    List.get (List.zipWith3 xs ys zs f) j = some3 f (List.get xs j) (List.get ys j) (List.get zs j)
  | Nil, ys, zs, j => rfl
  | Cons x xs, Nil, zs, j => Eq.sym (some3None2 f _ _)
  | Cons x xs, Cons y ys, Nil, j => Eq.sym (some3None3 f _ _)
  | Cons x xs, Cons y ys, Cons z zs, Zero => rfl
  | Cons x xs, Cons y ys, Cons z zs, Succ j => getZipWith3 f xs ys zs j

-- Three lists zipped in step are no longer than the first.
theorem lengthZipWith3Le (f: a → b → c → d): (xs: List a) → (ys: List b) → (zs: List c) → List.length (List.zipWith3 xs ys zs f) ≤ List.length xs
  | Nil, ys, zs => rfl
  | Cons x xs, Nil, zs => rfl
  | Cons x xs, Cons y ys, Nil => rfl
  | Cons x xs, Cons y ys, Cons z zs => lengthZipWith3Le f xs ys zs

theorem zipWith3Nil2 (zs: List c) (f: a → b → c → d): (xs: List a) → List.zipWith3 xs Nil zs f = Nil
  | Nil => rfl
  | Cons x xs => rfl

theorem zipWith3Nil3 (f: a → b → c → d): (xs: List a) → (ys: List b) → List.zipWith3 xs ys Nil f = Nil
  | Nil, ys => rfl
  | Cons x xs, Nil => rfl
  | Cons x xs, Cons y ys => rfl

-- `f` of two elements when both are there, otherwise 0.
def at2 (f: a → b → Nat): Option a → Option b → Nat
  | Some x, Some y => f x y
  | _, _ => 0

theorem at2None2 (f: a → b → Nat): (x: Option a) → at2 f x None = 0
  | None => rfl
  | Some x => rfl

-- The same for two lists.
theorem sumByZipWith (g: c → Nat) (f: a → b → c): (as: List a) → (bs: List b) → (n: Nat) → List.length as ≤ n →
    List.sumBy (List.zipWith as bs f) g = List.sumBy (List.range n) (j => at2 (x y => g (f x y)) (List.get as j) (List.get bs j))
  | Nil, bs, n, h => Eq.sym (sumRangeZero _ n (j => rfl))
  | Cons x xs, Nil, n, h => Eq.sym (sumRangeZero _ n (j => at2None2 _ _))
  | Cons x xs, Cons y ys, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Cons y ys, Succ n, h =>
    let each := (j: Nat) => at2 (x y => g (f x y)) (List.get (Cons x xs) j) (List.get (Cons y ys) j)
    calc List.sumBy (Cons (f x y) (List.zipWith xs ys f)) g
      _ = g (f x y) + List.sumBy (List.zipWith xs ys f) g := List.sumByCons (List.zipWith xs ys f) (f x y) g
      _ = each 0 + List.sumBy (List.range n) (j => each (Succ j)) := rewrite sumByZipWith g f xs ys n h
      _ = List.sumBy (List.range (Succ n)) each := Eq.sym (List.sumByRangeSucc each n)

-- `at3` of optional elements is `f` of them with defaults for the missing
-- ones, when a default anywhere makes `f` 0.
theorem at3OrElse (f: a → b → c → Nat) (da: a) (db: b) (dc: c)
    (zero1: (y: b) → (z: c) → f da y z = 0)
    (zero2: (x: a) → (z: c) → f x db z = 0)
    (zero3: (x: a) → (y: b) → f x y dc = 0):
    (oa: Option a) → (ob: Option b) → (oc: Option c) →
    at3 f oa ob oc = f (Option.getOrElse oa da) (Option.getOrElse ob db) (Option.getOrElse oc dc)
  | None, ob, oc => Eq.sym (zero1 _ _)
  | Some x, None, oc => Eq.sym (zero2 _ _)
  | Some x, Some y, None => Eq.sym (zero3 _ _)
  | Some x, Some y, Some z => rfl
