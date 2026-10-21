-- `Vec a n`: lists of exactly n elements, as an indexed data type (Agda's
-- `Vec`, Idris's `Vect`). Matching `VCons` tells the checker the length is a
-- successor, so `head` needs no default and `zipWith` needs no arm for
-- vectors of different lengths. Indexing is by `Fin n` (`Vec.get`), or by a
-- `Nat` with a proof that it is in range (`Vec.getLt`). The lemmas connect a
-- vector to its `toList`, so the list lemmas apply to it, and give `get` of
-- each operation. docs/proposals/vec.md.

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

-- The length, which the type already says.
def Vec.length (v: Vec a n): Nat := n

def Vec.head: Vec a (Succ n) -> a
  | VCons x _ => x

def Vec.tail: Vec a (Succ n) -> Vec a n
  | VCons _ xs => xs

-- The first element, or `d` if there is none: for a look ahead along a
-- vector of unknown length.
def Vec.headOr (d: a): Vec a n -> a
  | VNil      => d
  | VCons x _ => x

-- n copies of x.
def Vec.replicate: (n: Nat) -> a -> Vec a n
  | Zero,   _ => VNil
  | Succ k, x => VCons x (Vec.replicate k x)

def Vec.map (f: a -> b): Vec a n -> Vec b n
  | VNil       => VNil
  | VCons x xs => VCons (f x) (Vec.map f xs)

def Vec.zipWith (f: a -> b -> c): Vec a n -> Vec b n -> Vec c n
  | VNil,       VNil       => VNil
  | VCons x xs, VCons y ys => VCons (f x y) (Vec.zipWith f xs ys)

def Vec.zipWith3 (f: a -> b -> c -> d): Vec a n -> Vec b n -> Vec c n -> Vec d n
  | VNil,       VNil,       VNil       => VNil
  | VCons x xs, VCons y ys, VCons z zs => VCons (f x y z) (Vec.zipWith3 f xs ys zs)

-- Left fold; tail-recursive. `Vec.foldLeft f z [x, y]` is `f (f z x) y`.
def Vec.foldLeft (f: b -> a -> b) (z: b): Vec a n -> b
  | VNil       => z
  | VCons x xs => Vec.foldLeft f (f z x) xs

def Vec.sum (v: Vec Nat n): Nat := Vec.foldLeft Nat.add 0 v

-- The sum of `f` over the elements, as `List.sumBy`.
def Vec.sumBy (f: a -> Nat) (v: Vec a n): Nat := Vec.foldLeft (acc x => acc + f x) 0 v

def Vec.toList: Vec a n -> List a
  | VNil       => Nil
  | VCons x xs => Cons x (Vec.toList xs)

-- A list as a vector of its length, given the length: each `VCons` stores
-- `k`, a number already computed. (Building `VCons x (fromList xs)` against
-- the type `Vec a (List.length (Cons x xs))` would store `List.length xs`
-- at every element, which is quadratic: indexed-families.md §8.1.)
def Vec.fromListN: (n: Nat) -> (xs: List a) -> List.length xs = n -> Vec a n
  | Zero,   Nil,       _  => VNil
  | Succ k, Cons x xs, ok => VCons [n := k] x (Vec.fromListN k xs (Nat.succInjective (List.length xs) k ok))
  | Zero,   Cons x xs, ok => Void.absurd (Nat.succNotZero (List.length xs) ok)
  | Succ k, Nil,       ok => Void.absurd (Nat.zeroNotSucc k ok)

def Vec.fromList (xs: List a): Vec a (List.length xs) := Vec.fromListN (List.length xs) xs rfl

-- The list as a vector of length n, or `Nothing` if its length isn't n.
def Vec.ofList: (n: Nat) -> List a -> Maybe (Vec a n)
  | Zero,   Nil       => Just VNil
  | Succ k, Cons x xs => Maybe.map (rest => VCons x rest) (Vec.ofList k xs)
  | _,      _         => Nothing

-- `f` of every element, or `Nothing` if any is `Nothing`: parsing a vector
-- of lines into a vector of rows of a fixed width.
def Vec.traverseMaybe (f: a -> Maybe b): Vec a n -> Maybe (Vec b n)
  | VNil       => Just VNil
  | VCons x xs => Maybe.andThen (y => Maybe.map (ys => VCons y ys) (Vec.traverseMaybe f xs)) (f x)

-- The element at a position.
def Vec.get: Vec a n -> Fin n -> a
  | VCons x _,  FZero   => x
  | VCons _ xs, FSucc i => Vec.get xs i

-- The element at a `Nat` index in range: `Vec.getLt v 2` when `v` is known
-- to be longer than 2, or with the proof passed by name.
def Vec.getLt (v: Vec a n) (i: Nat) [auto ok: i < n]: a := Vec.get v (Fin.ofNatLt n i ok)

-- Whether some element satisfies `p`.
def Vec.any (p: a -> Bool): Vec a n -> Bool
  | VNil       => False
  | VCons x xs => p x || Vec.any p xs

-- Lemmas: `toList`.

theorem Vec.lengthToList: (v: Vec a n) -> List.length (Vec.toList v) = n
  | VNil       => rfl
  | VCons x xs => Eq.cong Succ (Vec.lengthToList xs)

-- Vectors with the same list are equal (so `Vec.toList u == Vec.toList v`
-- decides `u = v`).
theorem Vec.toListInjective: (u: Vec a n) -> (v: Vec a n) -> Vec.toList u = Vec.toList v -> u = v
  | VNil,       VNil,       h => rfl
  | VCons x xs, VCons y ys, h =>
    Eq.trans (Eq.cong (z => VCons z xs) (Eq.cong (List.headOr x) h))
      (Eq.cong (VCons y) (Vec.toListInjective xs ys (Eq.cong List.tailOf h)))

-- `==` on vectors: they're equal exactly when their lists are. A library
-- file may declare instances for its own types: they're loaded with the
-- type, so they're there wherever a vector is (docs/proposals/interfaces.md,
-- "As built (stage 2)").
instance Vec.instDecEq [auto decEq: DecEq a]: DecEq (Vec a n) :=
  { decide = u v =>
      if h: Vec.toList u = Vec.toList v then Yes (Vec.toListInjective u v h)
      else No (e => h (Eq.cong Vec.toList e)) }

theorem Vec.toListFromListN: (n: Nat) -> (xs: List a) -> (ok: List.length xs = n) -> Vec.toList (Vec.fromListN n xs ok) = xs
  | Zero,   Nil,       _  => rfl
  | Succ k, Cons x xs, ok => Eq.cong (Cons x) (Vec.toListFromListN k xs (Nat.succInjective (List.length xs) k ok))
  | Zero,   Cons x xs, ok => Void.exfalso (Nat.succNotZero (List.length xs) ok)
  | Succ k, Nil,       ok => Void.exfalso (Nat.zeroNotSucc k ok)

theorem Vec.toListFromList (xs: List a): Vec.toList (Vec.fromList xs) = xs := Vec.toListFromListN (List.length xs) xs rfl

theorem Vec.ofListCons (x: a) (y: a) (ys: Vec a k): (m: Maybe (Vec a k)) ->
    Maybe.map (rest => VCons x rest) m = Just (VCons y ys) -> And (x = y) (m = Just ys)
  | Nothing, h => Void.exfalso (Maybe.nothingNotJust (VCons y ys) h)
  | Just w,  h =>
    let e := Eq.cong (Maybe.withDefault (VCons x w)) h
    Both (Eq.cong Vec.head e) (Eq.cong Just (Eq.cong Vec.tail e))

-- What `ofList` accepts is the list it was given.
theorem Vec.ofListToList: (n: Nat) -> (xs: List a) -> (v: Vec a n) -> Vec.ofList n xs = Just v -> Vec.toList v = xs
  | Zero,   Nil,       VNil,       h => rfl
  | Succ k, Cons x xs, VCons y ys, h =>
    match Vec.ofListCons x y ys (Vec.ofList k xs) h with
      | Both xy rest => Eq.trans (Eq.cong (z => Cons z (Vec.toList ys)) (Eq.sym xy)) (Eq.cong (Cons x) (Vec.ofListToList k xs ys rest))
  | Zero,   Cons x xs, v,          h => Void.exfalso (Maybe.nothingNotJust v h)
  | Succ k, Nil,       v,          h => Void.exfalso (Maybe.nothingNotJust v h)

theorem Vec.toListReplicate (x: a): (n: Nat) -> Vec.toList (Vec.replicate n x) = List.replicate n x
  | Zero   => rfl
  | Succ k => Eq.cong (Cons x) (Vec.toListReplicate x k)

theorem Vec.toListMap (f: a -> b): (v: Vec a n) -> Vec.toList (Vec.map f v) = List.map f (Vec.toList v)
  | VNil       => rfl
  | VCons x xs => Eq.cong (Cons (f x)) (Vec.toListMap f xs)

theorem Vec.toListZipWith (f: a -> b -> c): (u: Vec a n) -> (v: Vec b n) ->
    Vec.toList (Vec.zipWith f u v) = List.zipWith f (Vec.toList u) (Vec.toList v)
  | VNil,       VNil       => rfl
  | VCons x xs, VCons y ys => Eq.cong (Cons (f x y)) (Vec.toListZipWith f xs ys)

theorem Vec.toListZipWith3 (f: a -> b -> c -> d): (u: Vec a n) -> (v: Vec b n) -> (w: Vec c n) ->
    Vec.toList (Vec.zipWith3 f u v w) = List.zipWith3 f (Vec.toList u) (Vec.toList v) (Vec.toList w)
  | VNil,       VNil,       VNil       => rfl
  | VCons x xs, VCons y ys, VCons z zs => Eq.cong (Cons (f x y z)) (Vec.toListZipWith3 f xs ys zs)

theorem Vec.foldLeftToList (f: b -> a -> b): (z: b) -> (v: Vec a n) -> Vec.foldLeft f z v = List.foldLeft f z (Vec.toList v)
  | z, VNil       => rfl
  | z, VCons x xs => Vec.foldLeftToList f (f z x) xs

theorem Vec.sumByToList (f: a -> Nat) (v: Vec a n): Vec.sumBy f v = List.sumBy f (Vec.toList v) :=
  Vec.foldLeftToList (acc x => acc + f x) 0 v

theorem Vec.sumToList (v: Vec Nat n): Vec.sum v = List.sum (Vec.toList v) := Vec.foldLeftToList Nat.add 0 v

-- What `traverseMaybe` accepts is `f` of each element.
theorem Vec.traverseMaybeCons (f: a -> Maybe b) (x: a) (xs: Vec a n) (y: b) (ys: Vec b n): (m: Maybe b) -> f x = m ->
    Vec.traverseMaybe f (VCons x xs) = Just (VCons y ys) -> And (f x = Just y) (Vec.traverseMaybe f xs = Just ys)
  | Nothing, e, h =>
    Void.exfalso (Maybe.nothingNotJust (VCons y ys)
      (Eq.trans (Eq.cong (Maybe.andThen (z => Maybe.map (zs => VCons z zs) (Vec.traverseMaybe f xs))) (Eq.sym e)) h))
  | Just z,  e, h =>
    let parts := Vec.ofListCons z y ys (Vec.traverseMaybe f xs)
      (Eq.trans (Eq.cong (Maybe.andThen (z => Maybe.map (zs => VCons z zs) (Vec.traverseMaybe f xs))) (Eq.sym e)) h)
    Both (Eq.trans e (Eq.cong Just (And.left parts))) (And.right parts)

theorem Vec.traverseMaybeGet (f: a -> Maybe b): (v: Vec a n) -> (out: Vec b n) -> Vec.traverseMaybe f v = Just out ->
    (i: Fin n) -> f (Vec.get v i) = Just (Vec.get out i)
  | VCons x xs, VCons y ys, h, FZero   => And.left (Vec.traverseMaybeCons f x xs y ys (f x) rfl h)
  | VCons x xs, VCons y ys, h, FSucc i => Vec.traverseMaybeGet f xs ys (And.right (Vec.traverseMaybeCons f x xs y ys (f x) rfl h)) i

-- Lemmas: `get`.

-- `get` is `List.getOr` on the list, whatever the default.
theorem Vec.getToList (d: a): (v: Vec a n) -> (i: Fin n) -> List.getOr d (Fin.toNat i) (Vec.toList v) = Vec.get v i
  | VCons x xs, FZero   => rfl
  | VCons x xs, FSucc i => Vec.getToList d xs i

theorem Vec.getReplicate (x: a): (n: Nat) -> (i: Fin n) -> Vec.get (Vec.replicate n x) i = x
  | _, FZero               => rfl
  | _, FSucc [n := k] i    => Vec.getReplicate x k i

theorem Vec.getMap (f: a -> b): (v: Vec a n) -> (i: Fin n) -> Vec.get (Vec.map f v) i = f (Vec.get v i)
  | VCons x xs, FZero   => rfl
  | VCons x xs, FSucc i => Vec.getMap f xs i

theorem Vec.getZipWith (f: a -> b -> c): (u: Vec a n) -> (v: Vec b n) -> (i: Fin n) ->
    Vec.get (Vec.zipWith f u v) i = f (Vec.get u i) (Vec.get v i)
  | VCons x xs, VCons y ys, FZero   => rfl
  | VCons x xs, VCons y ys, FSucc i => Vec.getZipWith f xs ys i

theorem Vec.getZipWith3 (f: a -> b -> c -> d): (u: Vec a n) -> (v: Vec b n) -> (w: Vec c n) -> (i: Fin n) ->
    Vec.get (Vec.zipWith3 f u v w) i = f (Vec.get u i) (Vec.get v i) (Vec.get w i)
  | VCons x xs, VCons y ys, VCons z zs, FZero   => rfl
  | VCons x xs, VCons y ys, VCons z zs, FSucc i => Vec.getZipWith3 f xs ys zs i

-- `headOr` is index 0 of the list.
theorem Vec.headOrToList (d: a): (v: Vec a n) -> Vec.headOr d v = List.getOr d 0 (Vec.toList v)
  | VNil       => rfl
  | VCons x xs => rfl

-- `getOr` on the list of a `zipWith3`, at any index, with defaults that
-- `f` maps to the default.
theorem Vec.getOrZipWith3 (f: a -> b -> c -> r) (d1: a) (d2: b) (d3: c) (d: r) (hd: f d1 d2 d3 = d):
    (u: Vec a n) -> (v: Vec b n) -> (w: Vec c n) -> (i: Nat) ->
    List.getOr d i (Vec.toList (Vec.zipWith3 f u v w)) = f (List.getOr d1 i (Vec.toList u)) (List.getOr d2 i (Vec.toList v)) (List.getOr d3 i (Vec.toList w))
  | VNil,       VNil,       VNil,       i      => Eq.sym hd
  | VCons x xs, VCons y ys, VCons z zs, Zero   => rfl
  | VCons x xs, VCons y ys, VCons z zs, Succ i => Vec.getOrZipWith3 f d1 d2 d3 d hd xs ys zs i

-- `any` is the list's.
theorem Vec.anyToList (p: a -> Bool): (v: Vec a n) -> Vec.any p v = List.any p (Vec.toList v)
  | VNil       => rfl
  | VCons x xs => Eq.cong (t => p x || t) (Vec.anyToList p xs)

-- Vectors that agree at every position are equal.
theorem Vec.ext: (u: Vec a n) -> (v: Vec a n) -> ((i: Fin n) -> Vec.get u i = Vec.get v i) -> u = v
  | VNil,       VNil,       h => rfl
  | VCons x xs, VCons y ys, h =>
    Eq.trans (Eq.cong (z => VCons z xs) (h FZero)) (Eq.cong (VCons y) (Vec.ext xs ys (i => h (FSucc i))))

def Vec.example: Vec Nat 3 := VCons 1 (VCons 2 (VCons 3 VNil))

theorem Vec.getLtExample: Vec.getLt Vec.example 2 = 3 := rfl

test "head and tail" := Vec.head Vec.example == 1 && Vec.head (Vec.tail Vec.example) == 2
test "length" := Vec.length Vec.example == 3
test "replicate" := Vec.toList (Vec.replicate 3 'x') == ['x', 'x', 'x']
test "map" := Vec.toList (Vec.map (x => x * 10) Vec.example) == [10, 20, 30]
test "zipWith" := Vec.toList (Vec.zipWith (x y => x + y) Vec.example Vec.example) == [2, 4, 6]
test "zipWith3" := Vec.toList (Vec.zipWith3 (x y z => x * y + z) Vec.example Vec.example Vec.example) == [2, 6, 12]
test "sum and sumBy" := Vec.sum Vec.example == 6 && Vec.sumBy (x => x * x) Vec.example == 14
test "fromList" := Vec.toList (Vec.fromList [4, 5]) == [4, 5] && Vec.length (Vec.fromList [4, 5]) == 2
test "ofList" := Maybe.map Vec.toList (Vec.ofList 2 [4, 5]) == Just [4, 5]
test "ofList refuses another length" := Maybe.map Vec.toList (Vec.ofList 3 [4, 5]) == Nothing
test "traverseMaybe" := Maybe.map Vec.toList (Vec.traverseMaybe (x => if x < 5 then Just (x + 1) else Nothing) Vec.example) == Just [2, 3, 4]
test "traverseMaybe fails" := Maybe.map Vec.toList (Vec.traverseMaybe (x => if x < 3 then Just x else Nothing) Vec.example) == Nothing
test "any" := Vec.any (x => x == 2) Vec.example && Bool.not (Vec.any (x => x == 4) Vec.example)
test "get" := Vec.get Vec.example (FSucc FZero) == 2 && Vec.getLt Vec.example 0 == 1
