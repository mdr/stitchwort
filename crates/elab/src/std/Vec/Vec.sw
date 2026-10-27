-- `Vec a n`: lists of exactly n elements, as an indexed data type (Agda's
-- `Vec`, Idris's `Vect`). Matching `VCons` tells the checker the length is a
-- successor, so `head` needs no default and `zipWith` needs no arm for
-- vectors of different lengths. Indexing is by `Fin n` (`Vec.get`), or by a
-- `Nat` with a proof that it is in range (`Vec.getLt`). The lemmas connect a
-- vector to its `toList`, so the list lemmas apply to it, and give `get` of
-- each operation. docs/proposals/vec.md.

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

-- The length, which the type already says.
def Vec.length (v: Vec a n): Nat := n

def Vec.head: Vec a (Succ n) → a
  | VCons x _ => x

def Vec.tail: Vec a (Succ n) → Vec a n
  | VCons _ xs => xs

-- The first element, or `fallback` if there is none: for a look ahead along a
-- vector of unknown length.
def Vec.headOr: Vec a n → (fallback: a) → a
  | VNil, fallback => fallback
  | VCons x _, fallback => x

-- n copies of x.
def Vec.replicate: (n: Nat) → a → Vec a n
  | Zero, _ => VNil
  | Succ k, x => VCons x (Vec.replicate k x)

-- A vector from a function of the position: `Vec.tabulate 3 f` is
-- `[f 0, f 1, f 2]` (Lean's `Vector.ofFn`, Agda's `tabulate`). The position
-- is a `Fin n`, as `Vec.get` takes, so `Vec.get (Vec.tabulate n f) i` is
-- `f i`; `Fin.toNat` gives its number.
def Vec.tabulate: (n: Nat) → (f: Fin n → a) → Vec a n
  | Zero, f => VNil
  | Succ k, f => VCons (f FZero) (Vec.tabulate k (i => f (FSucc i)))

def Vec.map: Vec a n → (f: a → b) → Vec b n
  | VNil, f => VNil
  | VCons x xs, f => VCons (f x) (Vec.map xs f)

def Vec.zipWith: Vec a n → Vec b n → (f: a → b → c) → Vec c n
  | VNil, VNil, f => VNil
  | VCons x xs, VCons y ys, f => VCons (f x y) (Vec.zipWith xs ys f)

def Vec.zipWith3: Vec a n → Vec b n → Vec c n → (f: a → b → c → d) → Vec d n
  | VNil, VNil, VNil, f => VNil
  | VCons x xs, VCons y ys, VCons z zs, f => VCons (f x y z) (Vec.zipWith3 xs ys zs f)

-- Left fold; tail-recursive. `Vec.foldLeft [x, y] initial f` is `f (f initial x) y`.
def Vec.foldLeft: Vec a n → (initial: b) → (f: b → a → b) → b
  | VNil, initial, f => initial
  | VCons x xs, initial, f => Vec.foldLeft xs (f initial x) f

def Vec.sum (v: Vec Nat n): Nat := Vec.foldLeft v 0 Nat.add

-- The sum of `f` over the elements, as `List.sumBy`.
def Vec.sumBy (v: Vec a n) (f: a → Nat): Nat := Vec.foldLeft v 0 (acc x => acc + f x)

-- How many elements satisfy `p`, as `List.count`.
def Vec.count (v: Vec a n) (p: a → Bool): Nat := Vec.foldLeft v 0 (k x => Nat.succIf k (p x))

def Vec.toList: Vec a n → List a
  | VNil => Nil
  | VCons x xs => Cons x (Vec.toList xs)

-- A list as a vector of its length, given the length: each `VCons` stores
-- `k`, a number already computed. (Building `VCons x (fromList xs)` against
-- the type `Vec a (List.length (Cons x xs))` would store `List.length xs`
-- at every element, which is quadratic: indexed-families.md §8.1.)
def Vec.fromListN: (n: Nat) → (xs: List a) → List.length xs = n → Vec a n
  | Zero, Nil, _ => VNil
  | Succ k, Cons x xs, ok => VCons [n := k] x (Vec.fromListN k xs (Nat.succInjective (List.length xs) k ok))
  | Zero, Cons x xs, ok => Void.absurd (Nat.succNotZero (List.length xs) ok)
  | Succ k, Nil, ok => Void.absurd (Nat.zeroNotSucc k ok)

def Vec.fromList (xs: List a): Vec a (List.length xs) := Vec.fromListN (List.length xs) xs rfl

-- The list as a vector of length n, given whether its length is n.
def Vec.ofListDec (n: Nat) (xs: List a): Decidable (List.length xs = n) → Option (Vec a n)
  | Yes ok => Some (Vec.fromListN n xs ok)
  | No r => None

-- The list as a vector of length n, or `None` if its length isn't n. Two
-- loops, `List.length` then `Vec.fromListN`, so stack-safe on long lists.
def Vec.ofList (n: Nat) (xs: List a): Option (Vec a n) := Vec.ofListDec n xs (Nat.decEq (List.length xs) n)

-- `f` of every element, or `None` if any is `None`: parsing a vector
-- of lines into a vector of rows of a fixed width. A loop into a list, then
-- `Vec.ofList`, so stack-safe on long vectors; `Vec.traverseOptionVCons` is
-- its step.
def Vec.traverseOption (v: Vec a n) (f: a → Option b): Option (Vec b n) :=
  Option.flatMap (Vec.traverseOptionLoop f Nil v) (Vec.ofList n)

-- The loop of `Vec.traverseOption`: `done` holds the values so far, last
-- first. It stops at the first `None`.
@[noReceiver]
def Vec.traverseOptionLoop (f: a → Option b) (done: List b): Vec a k → Option (List b)
  | VNil => Some (List.reverseOnto done Nil)
  | VCons x xs =>
    match f x with
      | Some y => Vec.traverseOptionLoop f (Cons y done) xs
      | None => None

-- The element at a position.
def Vec.get: Vec a n → Fin n → a
  | VCons x _, FZero => x
  | VCons _ xs, FSucc i => Vec.get xs i

-- The element at a `Nat` index in range: `Vec.getLt v 2` when `v` is known
-- to be longer than 2, or with the proof passed by name.
def Vec.getLt (v: Vec a n) (i: Nat) [auto ok: i < n]: a := Vec.get v (Fin.ofNatLt n i ok)

-- The element at a `Nat` index, or `d` past the end: `Vec.getOr [7, 8] 1 0`
-- is 8 and `Vec.getOr [7, 8] 5 0` is 0. No proof that the index is in range,
-- so a proof about one column of a grid can read every row at it. It is
-- `List.getOr` of the `toList`; the lemmas below give it for each operation.
def Vec.getOr (v: Vec a n) (i: Nat) (d: a): a := List.getOr (Vec.toList v) i d

-- Whether some element satisfies `p`.
def Vec.any: Vec a n → (p: a → Bool) → Bool
  | VNil, p => False
  | VCons x xs, p => p x ∨ Vec.any xs p

-- Lemmas: `toList`.

theorem Vec.lengthToList: (v: Vec a n) → List.length (Vec.toList v) = n
  | VNil => rfl
  | VCons x xs => Eq.cong Succ (Vec.lengthToList xs)

-- Vectors with the same list are equal (so `Vec.toList u == Vec.toList v`
-- decides `u = v`).
theorem Vec.toListInjective: (u: Vec a n) → (v: Vec a n) → Vec.toList u = Vec.toList v → u = v
  | VNil, VNil, h => rfl
  | VCons x xs, VCons y ys, h =>
    Eq.trans (Eq.cong (z => VCons z xs) (Eq.cong (.headOr x) h))
      (Eq.cong (VCons y) (Vec.toListInjective xs ys (Eq.cong List.tailOf h)))

-- `==` on vectors: they're equal exactly when their lists are. A library
-- file may declare instances for its own types: they're loaded with the
-- type, so they're there wherever a vector is (docs/proposals/interfaces.md,
-- "As built (stage 2)").
instance Vec.instDecEq [auto decEq: DecEq a]: DecEq (Vec a n) :=
  { decide = u v =>
    if h: Vec.toList u = Vec.toList v then Yes (Vec.toListInjective u v h)
    else No (e => h (Eq.cong Vec.toList e)) }

-- Vectors in order: lexicographic, as their lists (`List.instOrd`).
instance Vec.instOrd [auto ord: Ord a]: Ord (Vec a n) := Ord.byKey Vec.toList Vec.toListInjective

theorem Vec.toListFromListN: (n: Nat) → (xs: List a) → (ok: List.length xs = n) → Vec.toList (Vec.fromListN n xs ok) = xs
  | Zero, Nil, _ => rfl
  | Succ k, Cons x xs, ok => Eq.cong (Cons x) (Vec.toListFromListN k xs (Nat.succInjective (List.length xs) k ok))
  | Zero, Cons x xs, ok => Void.exfalso (Nat.succNotZero (List.length xs) ok)
  | Succ k, Nil, ok => Void.exfalso (Nat.zeroNotSucc k ok)

theorem Vec.toListFromList (xs: List a): Vec.toList (Vec.fromList xs) = xs := Vec.toListFromListN (List.length xs) xs rfl

theorem Vec.ofListCons (x: a) (y: a) (ys: Vec a k): (m: Option (Vec a k)) →
    Option.map m (rest => VCons x rest) = Some (VCons y ys) → And (x = y) (m = Some ys)
  | None, h => Void.exfalso (Option.noneNotSome (VCons y ys) h)
  | Some w, h =>
    let e := Eq.cong (.getOrElse (VCons x w)) h
    Both (Eq.cong Vec.head e) (Eq.cong Some (Eq.cong Vec.tail e))

theorem Vec.ofListDecToList (n: Nat) (xs: List a) (v: Vec a n): (d: Decidable (List.length xs = n)) → Vec.ofListDec n xs d = Some v → Vec.toList v = xs
  | Yes ok, h => Eq.trans (Eq.cong Vec.toList (Eq.sym (Eq.cong (.getOrElse (Vec.fromListN n xs ok)) h))) (Vec.toListFromListN n xs ok)
  | No r, h => Void.exfalso (Option.noneNotSome v h)

-- What `ofList` accepts is the list it was given.
theorem Vec.ofListToList (n: Nat) (xs: List a) (v: Vec a n) (h: Vec.ofList n xs = Some v): Vec.toList v = xs :=
  Vec.ofListDecToList n xs v (Nat.decEq (List.length xs) n) h

theorem Vec.toListReplicate (x: a): (n: Nat) → Vec.toList (Vec.replicate n x) = List.replicate n x
  | Zero => rfl
  | Succ k => Eq.cong (Cons x) (Vec.toListReplicate x k)

theorem Vec.toListMap: (v: Vec a n) → (f: a → b) → Vec.toList (Vec.map v f) = List.map (Vec.toList v) f
  | VNil, f => rfl
  | VCons x xs, f => Eq.cong (Cons (f x)) (Vec.toListMap xs f)

theorem Vec.toListZipWith: (u: Vec a n) → (v: Vec b n) → (f: a → b → c) →
    Vec.toList (Vec.zipWith u v f) = List.zipWith (Vec.toList u) (Vec.toList v) f
  | VNil, VNil, f => rfl
  | VCons x xs, VCons y ys, f => Eq.cong (Cons (f x y)) (Vec.toListZipWith xs ys f)

theorem Vec.toListZipWith3: (u: Vec a n) → (v: Vec b n) → (w: Vec c n) → (f: a → b → c → d) →
    Vec.toList (Vec.zipWith3 u v w f) = List.zipWith3 (Vec.toList u) (Vec.toList v) (Vec.toList w) f
  | VNil, VNil, VNil, f => rfl
  | VCons x xs, VCons y ys, VCons z zs, f => Eq.cong (Cons (f x y z)) (Vec.toListZipWith3 xs ys zs f)

theorem Vec.foldLeftToList: (v: Vec a n) → (z: b) → (f: b → a → b) → Vec.foldLeft v z f = List.foldLeft (Vec.toList v) z f
  | VNil, z, f => rfl
  | VCons x xs, z, f => Vec.foldLeftToList xs (f z x) f

theorem Vec.sumByToList (v: Vec a n) (f: a → Nat): Vec.sumBy v f = List.sumBy (Vec.toList v) f :=
  Vec.foldLeftToList v 0 (acc x => acc + f x)

theorem Vec.sumToList (v: Vec Nat n): Vec.sum v = List.sum (Vec.toList v) := Vec.foldLeftToList v 0 Nat.add

-- The proof of the length doesn't matter.
theorem Vec.fromListNProofs (n: Nat) (xs: List a) (p: List.length xs = n) (q: List.length xs = n): Vec.fromListN n xs p = Vec.fromListN n xs q :=
  Vec.toListInjective (Vec.fromListN n xs p) (Vec.fromListN n xs q)
    (Eq.trans (Vec.toListFromListN n xs p) (Eq.sym (Vec.toListFromListN n xs q)))

theorem Vec.ofListDecSucc (y: a) (zs: List a) (k: Nat): (d: Decidable (List.length zs = k)) → (d2: Decidable (List.length (Cons y zs) = Succ k)) →
    Vec.ofListDec (Succ k) (Cons y zs) d2 = Option.map (Vec.ofListDec k zs d) (ys => VCons y ys)
  | Yes ok, Yes ok2 => Eq.cong Some (Eq.cong (VCons y) (Vec.fromListNProofs k zs (Nat.succInjective (List.length zs) k ok2) ok))
  | Yes ok, No r => Void.exfalso (r (Eq.cong Succ ok))
  | No r, Yes ok2 => Void.exfalso (r (Nat.succInjective (List.length zs) k ok2))
  | No r, No r2 => rfl

-- `ofList` of a list one longer: its tail's vector, with the head in front.
theorem Vec.ofListSucc (y: a) (zs: List a) (k: Nat): Vec.ofList (Succ k) (Cons y zs) = Option.map (Vec.ofList k zs) (ys => VCons y ys) :=
  Vec.ofListDecSucc y zs k (Nat.decEq (List.length zs) k) (Nat.decEq (List.length (Cons y zs)) (Succ k))

-- The values done so far go in front of what the rest gives.
theorem Vec.traverseOptionLoopDone (f: a → Option b): (v: Vec a k) → (done: List b) →
    Vec.traverseOptionLoop f done v = Option.map (Vec.traverseOptionLoop f Nil v) (ys => List.reverseOnto done ys)
  | VNil, done => rfl
  | VCons x xs, done =>
    match e: f x with
      | Some y =>
        rewrite Vec.traverseOptionLoopDone f xs (Cons y done), Vec.traverseOptionLoopDone f xs (Cons y Nil),
          Option.mapMap (ys => List.reverseOnto (Cons y Nil) ys) (ys => List.reverseOnto done ys) (Vec.traverseOptionLoop f Nil xs) in rfl
      | None => rfl

theorem Vec.traverseOptionStep (y: b) (k: Nat): (m: Option (List b)) →
    Option.flatMap (Option.map m (ys => List.reverseOnto (Cons y Nil) ys)) (Vec.ofList (Succ k))
      = Option.map (Option.flatMap m (Vec.ofList k)) (ys => VCons y ys)
  | None => rfl
  | Some zs => Vec.ofListSucc y zs k

-- The step of `traverseOption`, which the loop form hides.
theorem Vec.traverseOptionVCons (f: a → Option b) (x: a) (xs: Vec a k):
    Vec.traverseOption (VCons x xs) f = Option.flatMap (f x) (y => Option.map (Vec.traverseOption xs f) (ys => VCons y ys)) :=
  match e: f x with
    | Some y =>
      rewrite Vec.traverseOptionLoopDone f xs (Cons y Nil) in Vec.traverseOptionStep y k (Vec.traverseOptionLoop f Nil xs)
    | None => rfl

-- What `traverseOption` accepts is `f` of each element.
theorem Vec.traverseOptionCons (f: a → Option b) (x: a) (xs: Vec a n) (y: b) (ys: Vec b n): (m: Option b) → f x = m →
    Vec.traverseOption (VCons x xs) f = Some (VCons y ys) → And (f x = Some y) (Vec.traverseOption xs f = Some ys)
  | None, e, h =>
    Void.exfalso (Option.noneNotSome (VCons y ys)
      (Eq.trans (Eq.cong (.flatMap (z => Option.map (Vec.traverseOption xs f) (zs => VCons z zs))) (Eq.sym e))
        (Eq.trans (Eq.sym (Vec.traverseOptionVCons f x xs)) h)))
  | Some z, e, h =>
    let parts := Vec.ofListCons z y ys (Vec.traverseOption xs f)
      (Eq.trans (Eq.cong (.flatMap (z => Option.map (Vec.traverseOption xs f) (zs => VCons z zs))) (Eq.sym e))
        (Eq.trans (Eq.sym (Vec.traverseOptionVCons f x xs)) h))
    Both (Eq.trans e (Eq.cong Some (And.left parts))) (And.right parts)

theorem Vec.traverseOptionGet (f: a → Option b): (v: Vec a n) → (out: Vec b n) → Vec.traverseOption v f = Some out →
    (i: Fin n) → f (Vec.get v i) = Some (Vec.get out i)
  | VCons x xs, VCons y ys, h, FZero => And.left (Vec.traverseOptionCons f x xs y ys (f x) rfl h)
  | VCons x xs, VCons y ys, h, FSucc i => Vec.traverseOptionGet f xs ys (And.right (Vec.traverseOptionCons f x xs y ys (f x) rfl h)) i

-- Lemmas: `get`.

-- `get` is `List.getOr` on the list, whatever the default.
theorem Vec.getToList: (v: Vec a n) → (i: Fin n) → (d: a) → List.getOr (Vec.toList v) (Fin.toNat i) d = Vec.get v i
  | VCons x xs, FZero, d => rfl
  | VCons x xs, FSucc i, d => Vec.getToList xs i d

theorem Vec.getReplicate (x: a): (n: Nat) → (i: Fin n) → Vec.get (Vec.replicate n x) i = x
  | _, FZero => rfl
  | _, FSucc [n := k] i => Vec.getReplicate x k i

theorem Vec.getMap: (v: Vec a n) → (i: Fin n) → (f: a → b) → Vec.get (Vec.map v f) i = f (Vec.get v i)
  | VCons x xs, FZero, f => rfl
  | VCons x xs, FSucc i, f => Vec.getMap xs i f

theorem Vec.getZipWith: (u: Vec a n) → (v: Vec b n) → (i: Fin n) → (f: a → b → c) →
    Vec.get (Vec.zipWith u v f) i = f (Vec.get u i) (Vec.get v i)
  | VCons x xs, VCons y ys, FZero, f => rfl
  | VCons x xs, VCons y ys, FSucc i, f => Vec.getZipWith xs ys i f

theorem Vec.getZipWith3: (u: Vec a n) → (v: Vec b n) → (w: Vec c n) → (i: Fin n) → (f: a → b → c → d) →
    Vec.get (Vec.zipWith3 u v w f) i = f (Vec.get u i) (Vec.get v i) (Vec.get w i)
  | VCons x xs, VCons y ys, VCons z zs, FZero, f => rfl
  | VCons x xs, VCons y ys, VCons z zs, FSucc i, f => Vec.getZipWith3 xs ys zs i f

theorem Vec.getTabulate: (n: Nat) → (f: Fin n → a) → (i: Fin n) → Vec.get (Vec.tabulate n f) i = f i
  | _, f, FZero => rfl
  | _, f, FSucc [n := k] i => Vec.getTabulate k (j => f (FSucc j)) i

-- `any` is the list's.
theorem Vec.anyToList: (v: Vec a n) → (p: a → Bool) → Vec.any v p = List.any (Vec.toList v) p
  | VNil, p => rfl
  | VCons x xs, p => Eq.cong (t => p x ∨ t) (Vec.anyToList xs p)

-- Vectors that agree at every position are equal.
theorem Vec.ext: (u: Vec a n) → (v: Vec a n) → ((i: Fin n) → Vec.get u i = Vec.get v i) → u = v
  | VNil, VNil, h => rfl
  | VCons x xs, VCons y ys, h =>
    Eq.trans (Eq.cong (z => VCons z xs) (h FZero)) (Eq.cong (VCons y) (Vec.ext xs ys (i => h (FSucc i))))

-- Lemmas: `getOr`, index i of each operation. The defaults are what the
-- operation makes of the inputs' defaults, so the lemmas hold at every
-- index, past the end too, unless they say `i < n`.

-- In range, `getOr` is `get`, whatever the default.
theorem Vec.getOrGet (v: Vec a n) (i: Fin n) (d: a): Vec.getOr v (Fin.toNat i) d = Vec.get v i := Vec.getToList v i d

-- Past the end, `getOr` is the default.
theorem Vec.getOrPast (v: Vec a n) (i: Nat) (d: a) (h: n ≤ i): Vec.getOr v i d = d :=
  List.getOrPast (Vec.toList v) i d (rewrite Vec.lengthToList v in h)

-- `headOr` is index 0.
theorem Vec.headOrGetOr: (v: Vec a n) → (d: a) → Vec.headOr v d = Vec.getOr v 0 d
  | VNil, d => rfl
  | VCons x xs, d => rfl

-- Copies of x, read with x as the default, are x everywhere.
theorem Vec.getOrReplicate (x: a): (n: Nat) → (i: Nat) → Vec.getOr (Vec.replicate n x) i x = x
  | Zero, i => rfl
  | Succ k, Zero => rfl
  | Succ k, Succ i => Vec.getOrReplicate x k i

theorem Vec.getOrMap: (v: Vec a n) → (i: Nat) → (d: a) → (f: a → b) → Vec.getOr (Vec.map v f) i (f d) = f (Vec.getOr v i d)
  | VNil, i, d, f => rfl
  | VCons x xs, Zero, d, f => rfl
  | VCons x xs, Succ i, d, f => Vec.getOrMap xs i d f

-- `zipWith`, with defaults that `f` maps to the default (`f d1 d2 = d`,
-- often `rfl`).
theorem Vec.getOrZipWith (f: a → b → c) (d1: a) (d2: b) (d: c) (hd: f d1 d2 = d):
    (u: Vec a n) → (v: Vec b n) → (i: Nat) →
    Vec.getOr (Vec.zipWith u v f) i d = f (Vec.getOr u i d1) (Vec.getOr v i d2)
  | VNil, VNil, i => Eq.sym hd
  | VCons x xs, VCons y ys, Zero => rfl
  | VCons x xs, VCons y ys, Succ i => Vec.getOrZipWith f d1 d2 d hd xs ys i

-- `zipWith3`, with defaults that `f` maps to the default.
theorem Vec.getOrZipWith3 (f: a → b → c → r) (d1: a) (d2: b) (d3: c) (d: r) (hd: f d1 d2 d3 = d):
    (u: Vec a n) → (v: Vec b n) → (w: Vec c n) → (i: Nat) →
    Vec.getOr (Vec.zipWith3 u v w f) i d = f (Vec.getOr u i d1) (Vec.getOr v i d2) (Vec.getOr w i d3)
  | VNil, VNil, VNil, i => Eq.sym hd
  | VCons x xs, VCons y ys, VCons z zs, Zero => rfl
  | VCons x xs, VCons y ys, VCons z zs, Succ i => Vec.getOrZipWith3 f d1 d2 d3 d hd xs ys zs i

-- `tabulate` at an index in range.
theorem Vec.getOrTabulate (d: a): (n: Nat) → (f: Fin n → a) → (i: Nat) → (h: i < n) →
    Vec.getOr (Vec.tabulate n f) i d = f (Fin.ofNatLt n i h)
  | Zero, f, i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, f, Zero, h => rfl
  | Succ k, f, Succ i, h => Vec.getOrTabulate d k (j => f (FSucc j)) i h

-- A sum over the elements is a sum over the indices 0, 1, …, n - 1.
theorem Vec.sumByGetOr (v: Vec a n) (d: a) (f: a → Nat): Vec.sumBy v f = List.sumBy (List.range n) (i => f (Vec.getOr v i d)) :=
  calc Vec.sumBy v f
    _ = List.sumBy (Vec.toList v) f := Vec.sumByToList v f
    _ = List.sumBy (List.range (List.length (Vec.toList v))) (i => f (Vec.getOr v i d)) := List.sumByGetOr (Vec.toList v) d f
    _ = List.sumBy (List.range n) (i => f (Vec.getOr v i d)) := rewrite Vec.lengthToList v

-- Counting lemmas. A count is the list's count, a sum of 1s and 0s, and a
-- count of the indices 0, 1, …, n - 1 whose element satisfies `p`; it is at
-- most n.

theorem Vec.countToList (v: Vec a n) (p: a → Bool): Vec.count v p = List.count (Vec.toList v) p :=
  Vec.foldLeftToList v 0 (k x => Nat.succIf k (p x))

theorem Vec.countSumBy (v: Vec a n) (p: a → Bool): Vec.count v p = Vec.sumBy v (x => Bool.toNat (p x)) :=
  rewrite Vec.countToList v p, Vec.sumByToList v (x => Bool.toNat (p x)) in List.countSumBy (Vec.toList v) p

theorem Vec.countGetOr (v: Vec a n) (d: a) (p: a → Bool): Vec.count v p = List.count (List.range n) (i => p (Vec.getOr v i d)) :=
  rewrite Vec.countSumBy v p, Vec.sumByGetOr v d (x => Bool.toNat (p x)) in
    Eq.sym (List.countSumBy (List.range n) (i => p (Vec.getOr v i d)))

theorem Vec.countLe: (v: Vec a n) → (p: a → Bool) → Vec.count v p ≤ n
  | VNil, p => rfl
  | VCons x xs, p =>
    rewrite Vec.countToList (VCons x xs) p, List.countCons (Vec.toList xs) x p, <- Vec.countToList xs p in
      match p x with
        | True => omega [Vec.countLe xs p]
        | False => omega [Vec.countLe xs p]

-- Vectors that agree at every index are equal (one default for both).
theorem Vec.extGetOr (u: Vec a n) (d: a) (v: Vec a n) (h: (i: Nat) → Vec.getOr u i d = Vec.getOr v i d): u = v :=
  Vec.toListInjective u v
    (List.extGetOr d (Vec.toList u) (Vec.toList v) (rewrite Vec.lengthToList u, Vec.lengthToList v in rfl) (i hi => h i))

def Vec.example: Vec Nat 3 := VCons 1 (VCons 2 (VCons 3 VNil))

theorem Vec.getLtExample: Vec.getLt Vec.example 2 = 3 := rfl

theorem Vec.getOrExample: Vec.getOr Vec.example 2 0 = 3 := rfl

test "head and tail" := Vec.head Vec.example == 1 ∧ Vec.head (Vec.tail Vec.example) == 2
test "length" := Vec.length Vec.example == 3
test "replicate" := Vec.toList (Vec.replicate 3 'x') == ['x', 'x', 'x']
test "map" := Vec.toList (Vec.map Vec.example (* 10)) == [10, 20, 30]
test "zipWith" := Vec.toList (Vec.zipWith Vec.example Vec.example (+)) == [2, 4, 6]
test "zipWith3" := Vec.toList (Vec.zipWith3 Vec.example Vec.example Vec.example (x y z => x * y + z)) == [2, 6, 12]
test "sum and sumBy" := Vec.sum Vec.example == 6 ∧ Vec.sumBy Vec.example (x => x * x) == 14
test "fromList" := Vec.toList (Vec.fromList [4, 5]) == [4, 5] ∧ Vec.length (Vec.fromList [4, 5]) == 2
test "ofList" := Option.map (Vec.ofList 2 [4, 5]) Vec.toList == Some [4, 5]
test "ofList refuses another length" := Option.map (Vec.ofList 3 [4, 5]) Vec.toList == None
test "traverseOption" := Option.map (Vec.traverseOption Vec.example (x => if x < 5 then Some (x + 1) else None)) Vec.toList == Some [2, 3, 4]
test "traverseOption fails" := Option.map (Vec.traverseOption Vec.example (x => if x < 3 then Some x else None)) Vec.toList == None
test "any" := Vec.any Vec.example (== 2) ∧ ¬(Vec.any Vec.example (== 4))
test "get" := Vec.get Vec.example (FSucc FZero) == 2 ∧ Vec.getLt Vec.example 0 == 1
test "count" := Vec.count Vec.example (> 1) == 2 ∧ Vec.count Vec.example (> 3) == 0
test "count none" := Vec.count (VNil: Vec Nat 0) (> 1) == 0
test "count all" := Vec.count Vec.example (> 0) == 3
test "getOr" := Vec.getOr Vec.example 1 0 == 2 ∧ Vec.getOr Vec.example 3 0 == 0
test "getOr of map, zipWith and replicate" :=
  Vec.getOr (Vec.map Vec.example (* 10)) 1 0 == 20
    ∧ Vec.getOr (Vec.zipWith Vec.example Vec.example (+)) 2 0 == 6
    ∧ Vec.getOr (Vec.replicate 3 'x') 5 'x' == 'x'
test "tabulate" := Vec.toList (Vec.tabulate 4 (i => Fin.toNat i * 10)) == [0, 10, 20, 30]
test "tabulate none" := Vec.toList (Vec.tabulate 0 Fin.toNat) == []

theorem Vec.tabulateExample: Vec.toList (Vec.tabulate 3 Fin.toNat) = [0, 1, 2] := rfl

-- Like a list: `[1, 2, 3]`.
instance Vec.instShow [auto show: Show a]: Show (Vec a n) :=
  Show.fromText (v => Show.list (x => Show.toSource x) (Vec.toList v))
