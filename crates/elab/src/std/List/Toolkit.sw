-- The list toolkit: `map`, `filter`, folds, sums, `zip`, `take`/`drop`, `get`,
-- `splitBy`, padding, transpose and their lemmas. This file was the prelude's
-- "List toolkit" block and the list lemmas beside it.

theorem List.lengthAppend: (xs: List a) -> (ys: List a) -> List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil, ys => rfl
  | Cons x xs, ys => Eq.cong Succ (List.lengthAppend xs ys)

-- List toolkit. The callbacks are pure, except `List.map`'s, which may perform
-- abilities (docs/proposals/effect-polymorphism.md; more functions follow one
-- at a time). Every function is structurally recursive.

-- `f` on each element, in order. `f` may perform abilities, such as `Fail`:
-- `xs.map Range.read` fails at the first element that isn't a range
-- (docs/proposals/errors.md §3.4). With a pure `f` the row is empty and
-- `{e} b` is `b`, so this is the plain map: its lemmas are proved by
-- computation as before, and the backends compile it to the same loop.
def List.map (f: a -> {e} b): List a -> {e} List b
  | Nil => Nil
  | Cons x xs => Cons (f x) (List.map f xs)

-- One step of `List.filter`: `x` in front of the filtered rest, or not. A
-- function of its own so the recursive call is written once: with an `if`
-- around it in both branches, a condition the checker can't decide (one on
-- a variable) keeps both branches, and the value doubles with every element.
def List.filterStep (x: a) (rest: List a): Bool -> List a
  | True => Cons x rest
  | False => rest

def List.filter (p: a -> Bool): List a -> List a
  | Nil => Nil
  | Cons x xs => List.filterStep x (List.filter p xs) (p x)

-- Left fold; tail-recursive. `List.foldLeft f initial [x, y]` is `f (f initial x) y`.
def List.foldLeft (f: b -> a -> b) (initial: b): List a -> b
  | Nil => initial
  | Cons x xs => List.foldLeft f (f initial x) xs

-- Running accumulations, the initial value first (Haskell's `scanLeft`):
-- `List.scanLeft f initial [x, y]` is `[initial, f initial x, f (f initial x) y]`. Always one longer than
-- the input.
def List.scanLeft (f: b -> a -> b) (initial: b): List a -> List b
  | Nil => Cons initial Nil
  | Cons x xs => Cons initial (List.scanLeft f (f initial x) xs)

theorem List.scanLeftNil: List.scanLeft (acc x => acc + x) 5 Nil = [5] := rfl

theorem List.scanLeftSums: List.scanLeft (acc x => acc + x) 0 [1, 2, 3] = [0, 1, 3, 6] := rfl

-- Right fold. `List.foldRight f initial [x, y]` is `f x (f y initial)`. Runs
-- as a loop over the reversed list, so it is stack-safe on long lists.
def List.foldRight (f: a -> b -> b) (initial: b) (xs: List a): b := List.foldLeft (acc x => f x acc) initial (List.reverseOnto xs Nil)

theorem List.foldLeftReverseOnto (f: a -> b -> b) (z: b): (xs: List a) -> (acc: List a) ->
    List.foldLeft (r x => f x r) z (List.reverseOnto xs acc)
      = List.foldLeft (r x => f x r) (List.foldLeft (r x => f x r) z (List.reverseOnto xs Nil)) acc
  | Nil, acc => rfl
  | Cons x xs, acc =>
    Eq.trans (List.foldLeftReverseOnto f z xs (Cons x acc))
      (Eq.sym (Eq.cong (r => List.foldLeft (r2 y => f y r2) r acc) (List.foldLeftReverseOnto f z xs (Cons x Nil))))

-- The step of the right fold, which the loop form hides.
theorem List.foldRightCons (f: a -> b -> b) (z: b) (x: a) (xs: List a): List.foldRight f z (Cons x xs) = f x (List.foldRight f z xs) :=
  List.foldLeftReverseOnto f z xs (Cons x Nil)

-- The sum of the elements, of any type with `Add` (docs/proposals/interfaces.md
-- §7.7): `[1, 2, 3].sum` is `6`, `[3, -5, 1].sum` is `-1`.
def List.sum [auto add: Add a] (xs: List a): a := List.foldLeft Add.add Add.zero xs

-- The sum of `f` over the elements: `List.sumBy f xs` is `List.sum (List.map f xs)`
-- without building the intermediate list.
def List.sumBy [auto add: Add b] (f: a -> b) (xs: List a): b := List.foldLeft (acc x => acc + f x) Add.zero xs

theorem List.sumByDoubles: List.sumBy (x => x * 2) [1, 2, 3] = 12 := rfl

theorem List.sumInts: List.sum [(3: Int), -5, 1] = -1 := rfl

theorem List.sumByInts: List.sumBy (x => Int.sub 1 x) [1, 2, 3] = -3 := rfl

-- The product of the elements, of any type with `Mul`.
def List.product [auto mul: Mul a] (xs: List a): a := List.foldLeft Mul.mul Mul.one xs

def List.maximum [auto ord: Ord a]: List a -> Option a
  | Nil => None
  | Cons x xs => Some (List.foldLeft Ord.max x xs)

def List.minimum [auto ord: Ord a]: List a -> Option a
  | Nil => None
  | Cons x xs => Some (List.foldLeft Ord.min x xs)

-- Pairs up to the shorter list's length.
def List.zip: List a -> List b -> List (Pair a b)
  | Nil, ys => Nil
  | Cons x xs, Nil => Nil
  | Cons x xs, Cons y ys => Cons (MkPair x y) (List.zip xs ys)

def List.zipWith (f: a -> b -> c): List a -> List b -> List c
  | Nil, ys => Nil
  | Cons x xs, Nil => Nil
  | Cons x xs, Cons y ys => Cons (f x y) (List.zipWith f xs ys)

-- Combines three lists up to the shortest list's length.
def List.zipWith3 (f: a -> b -> c -> d): List a -> List b -> List c -> List d
  | Nil, ys, zs => Nil
  | Cons x xs, Nil, zs => Nil
  | Cons x xs, Cons y ys, Nil => Nil
  | Cons x xs, Cons y ys, Cons z zs => Cons (f x y z) (List.zipWith3 f xs ys zs)

-- The first n elements (all of them if there are fewer).
def List.take: Nat -> List a -> List a
  | Zero, xs => Nil
  | Succ n, Nil => Nil
  | Succ n, Cons x xs => Cons x (List.take n xs)

-- All but the first n elements.
def List.drop: Nat -> List a -> List a
  | Zero, xs => xs
  | Succ n, Nil => Nil
  | Succ n, Cons x xs => List.drop n xs

-- The element at index i, counting from 0.
def List.get: Nat -> List a -> Option a
  | i, Nil => None
  | Zero, Cons x xs => Some x
  | Succ i, Cons x xs => List.get i xs

def List.any (p: a -> Bool): List a -> Bool
  | Nil => False
  | Cons x xs => if p x then True else List.any p xs

def List.all (p: a -> Bool): List a -> Bool
  | Nil => True
  | Cons x xs => if p x then List.all p xs else False

-- `n`, plus one if `b`: `List.count`'s step. A function of its own so `n` is
-- written once: `if b then Succ n else n` writes it twice, so when the
-- checker can't decide the conditions, a count doubles in size with every
-- element.
def Nat.succIf (n: Nat): Bool -> Nat
  | True => Succ n
  | False => n

-- How many elements satisfy `p`.
def List.count (p: a -> Bool) (xs: List a): Nat := List.foldLeft (n x => Nat.succIf n (p x)) 0 xs

-- The first element satisfying `p`.
def List.find (p: a -> Bool): List a -> Option a
  | Nil => None
  | Cons x xs => if p x then Some x else List.find p xs

def List.consSome: Option b -> List b -> List b
  | None, rest => rest
  | Some y, rest => Cons y rest

-- Keeps the `Some` results, in order.
def List.filterMap (f: a -> Option b): List a -> List b
  | Nil => Nil
  | Cons x xs => List.consSome (f x) (List.filterMap f xs)

-- Joins a list of lists.
def List.concat: List (List a) -> List a
  | Nil => Nil
  | Cons xs xss => List.append xs (List.concat xss)

-- `List.replicate n x` is n copies of x.
def List.replicate: Nat -> a -> List a
  | Zero, x => Nil
  | Succ n, x => Cons x (List.replicate n x)

def List.rangeFrom: Nat -> Nat -> List Nat
  | Zero, i => Nil
  | Succ n, i => Cons i (List.rangeFrom n (Succ i))

-- A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend: (a: Nat) -> (b: Nat) -> (s: Nat) -> List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a))
  | Zero, b, s => Eq.cong (t => List.rangeFrom b t) (Eq.sym (Nat.addZero s))
  | Succ a, b, s =>
    Eq.cong (Cons s) (Eq.trans (List.rangeFromAppend a b (Succ s)) (Eq.cong (t => List.append (List.rangeFrom a (Succ s)) (List.rangeFrom b t)) (Eq.sym (Nat.addSucc s a))))

-- `List.range n` is `[0, 1, ..., n - 1]`.
def List.range (n: Nat): List Nat := List.rangeFrom n 0

-- `List.between lo hi` is `[lo, lo + 1, ..., hi]`, both ends included; empty
-- when `lo > hi`.
def List.between (lo: Nat) (hi: Nat): List Nat := List.rangeFrom (hi + 1 - lo) lo

-- `between` is a `rangeFrom` of the right length.
theorem List.betweenRangeFrom (lo: Nat) (hi: Nat): List.between lo hi = List.rangeFrom (hi + 1 - lo) lo := rfl

-- It has `hi + 1 - lo` elements: none when `lo > hi`, one when `lo = hi`.
theorem List.lengthBetween (lo: Nat) (hi: Nat): List.length (List.between lo hi) = hi + 1 - lo := List.lengthRangeFrom (hi + 1 - lo) lo

test "List.lengthBetween" := List.length (List.between 3 3) == 1 && List.length (List.between 5 2) == 0 && List.length (List.between 2 6) == 5
test "List.between, empty and single" := List.between 5 0 == Nil && List.between 0 0 == [0] && List.between 7 7 == [7]

def List.reverse (xs: List a): List a := List.reverseOnto xs Nil

def List.last: List a -> Option a
  | Nil => None
  | Cons x Nil => Some x
  | Cons x (Cons y ys) => List.last (Cons y ys)

-- The first element, or `None` for an empty list.
def List.head: List a -> Option a
  | Nil => None
  | Cons x xs => Some x

theorem List.headExample: List.head [3, 4] = Some 3 := rfl

theorem List.headEmpty: List.head (Nil: List Nat) = None := rfl

-- All but the last element (`Nil` for an empty list).
def List.init: List a -> List a
  | Nil => Nil
  | Cons x Nil => Nil
  | Cons x (Cons y ys) => Cons x (List.init (Cons y ys))

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := rfl

theorem List.initEmpty: List.init (Nil: List Nat) = Nil := rfl

-- Membership, given a decision for equality (as `List.decEq` takes).
def List.elem (decEq: (x: a) -> (y: a) -> Decidable (x = y)) (target: a): List a -> Bool
  | Nil => False
  | Cons x xs => if Decidable.toBool (decEq target x) then True else List.elem decEq target xs

-- The elements that satisfy `p`, and those that don't.
def List.partition (p: a -> Bool) (xs: List a): Pair (List a) (List a) := MkPair (List.filter p xs) (List.filter (x => !(p x)) xs)

-- The value for the first pair whose key is equal, given a decision for equality.
def List.lookup (decEq: (x: k) -> (y: k) -> Decidable (x = y)) (key: k): List (Pair k v) -> Option v
  | Nil => None
  | Cons (MkPair k v) rest => if Decidable.toBool (decEq key k) then Some v else List.lookup decEq key rest

-- `List.padRight n x xs` is `xs` followed by enough copies of `x` to make it
-- n long (it is `xs` itself when that is already n long or longer).
def List.padRight (n: Nat) (x: a) (xs: List a): List a := List.append xs (List.replicate (n - List.length xs) x)

theorem List.lengthReplicate (x: a): (n: Nat) -> List.length (List.replicate n x) = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (List.lengthReplicate x n)

-- Padding makes a list exactly n long, when it was no longer than that.
theorem List.padRightLength (n: Nat) (x: a) (xs: List a) (h: List.length xs <= n):
    List.length (List.padRight n x xs) = n :=
  Eq.trans (List.lengthAppend xs (List.replicate (n - List.length xs) x))
    (Eq.trans (Eq.cong (t => List.length xs + t) (List.lengthReplicate x (n - List.length xs)))
      (Nat.addSubCancel (List.length xs) n h))

-- The first `n` columns of a list of rows (`List.transpose`'s loop): column i
-- is the i-th element of each row that has one.
def List.transposeN: Nat -> List (List a) -> List (List a)
  | Zero, rows => Nil
  | Succ n, rows => Cons (List.filterMap (List.get 0) rows) (List.transposeN n (List.map (List.drop 1) rows))

-- Swaps rows and columns: the columns of a list of rows, as many as the first
-- row is long. For rows that are all the same length, the cell at row r and
-- column c moves to row c and column r. A row that's too short just leaves
-- its column out, and a row longer than the first loses its extra cells: the
-- result has the first row's width, so `[[1], [2, 3]].transpose` is
-- `[[1, 2]]` (Haskell's `transpose` goes to the longest row instead).
def List.transpose (rows: List (List a)): List (List a) := List.transposeN (List.length (List.headOr Nil rows)) rows

theorem List.padRightExample: List.padRight 4 0 [1, 2] = [1, 2, 0, 0] := rfl

theorem List.padRightLongEnough: List.padRight 1 0 [1, 2] = [1, 2] := rfl

-- Lemmas about `List.transpose`: it has as many columns as the first row is
-- long, and for a rectangular list, doing it twice gives back the list.
theorem List.lengthMap (f: a -> b): (xs: List a) -> List.length (List.map f xs) = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.lengthMap f xs)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := rfl

theorem List.transposeNone: List.transpose (Nil: List (List Nat)) = Nil := rfl

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := rfl

theorem List.transposeNLength: (n: Nat) -> (rows: List (List a)) -> List.length (List.transposeN n rows) = n
  | Zero, rows => rfl
  | Succ n, rows => Eq.cong Succ (List.transposeNLength n (List.map (List.drop 1) rows))

-- Every element of the list satisfies `p`.
def List.All (p: a -> Prop): List a -> Prop
  | Nil => Unit
  | Cons x xs => And (p x) (List.All p xs)

-- Some element of the list satisfies `p`.
def List.Any (p: a -> Prop): List a -> Prop
  | Nil => Void
  | Cons x xs => Or (p x) (List.Any p xs)

theorem List.allAppend (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p xs -> List.All p ys -> List.All p (List.append xs ys)
  | Nil, ys, hx, hy => hy
  | Cons x xs, ys, Both hx hxs, hy => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p (List.append xs ys) -> List.All p xs
  | Nil, ys, h => Trivial
  | Cons x xs, ys, Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p (List.append xs ys) -> List.All p ys
  | Nil, ys, h => h
  | Cons x xs, ys, Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap (p: b -> Prop) (f: a -> b): (xs: List a) -> List.All (x => p (f x)) xs -> List.All p (List.map f xs)
  | Nil, h => Trivial
  | Cons x xs, Both h hxs => Both h (List.allMap p f xs hxs)

theorem List.allImplies (p: a -> Prop) (q: a -> Prop) (h: (x: a) -> p x -> q x): (xs: List a) -> List.All p xs -> List.All q xs
  | Nil, hp => Trivial
  | Cons x xs, Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.Any p xs -> List.Any p (List.append xs ys)
  | Nil, ys, h => Void.exfalso h
  | Cons x xs, ys, Inl h => Inl h
  | Cons x xs, ys, Inr h => Inr (List.anyAppendLeft p xs ys h)

theorem List.anyAppendRight (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.Any p ys -> List.Any p (List.append xs ys)
  | Nil, ys, h => h
  | Cons x xs, ys, h => Inr (List.anyAppendRight p xs ys h)

-- `List.any` of two lists joined: either list has one.
theorem List.anyAppend (p: a -> Bool): (xs: List a) -> (ys: List a) -> List.any p (List.append xs ys) = (List.any p xs || List.any p ys)
  | Nil, ys => rfl
  | Cons x xs, ys =>
    match e: p x with
      | True => rfl
      | False => List.anyAppend p xs ys

theorem List.anyAppendExample: List.any (x => x == 3) (List.append [1, 2] [3]) = (False || True) := rfl

-- Every row has length n (the list is rectangular).
def List.AllLength (n: Nat): List (List a) -> Prop
  | Nil => Unit
  | Cons r rs => And (List.length r = n) (List.AllLength n rs)

theorem List.lengthZero: (xs: List a) -> List.length xs = 0 -> xs = Nil
  | Nil, h => rfl
  | Cons y ys, h => Void.exfalso (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil: (n: Nat) -> List.transposeN n (Nil: List (List a)) = List.replicate n Nil
  | Zero => rfl
  | Succ n => Eq.cong (Cons Nil) (List.transposeNNil n)

theorem List.allLengthZero: (rows: List (List a)) -> (n: Nat) -> List.length rows = n -> List.AllLength 0 rows ->
    rows = List.replicate n Nil
  | Nil, n, hl, hr => J (y q => (Nil: List (List a)) = List.replicate y (Nil: List a)) rfl hl
  | Cons r rs, Zero, hl, hr => Void.exfalso (Nat.succNotZero (List.length rs) hl)
  | Cons r rs, Succ m, hl, Both hr hrs =>
    Eq.trans (Eq.cong (t => Cons t rs) (List.lengthZero r hr))
      (Eq.cong (Cons Nil) (List.allLengthZero rs m (Nat.succInjective (List.length rs) m hl) hrs))

theorem List.tailsAllLength (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    List.AllLength k (List.map (List.drop 1) rows)
  | Nil, hr => Trivial
  | Cons Nil rs, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Both (Nat.succInjective (List.length ys) k hr) (List.tailsAllLength k rs hrs)

theorem List.headsLength (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    List.length (List.filterMap (List.get 0) rows) = List.length rows
  | Nil, hr => rfl
  | Cons Nil rs, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Eq.cong Succ (List.headsLength k rs hrs)

theorem List.rowsAreHeadsAndTails (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    rows = List.zipWith Cons (List.filterMap (List.get 0) rows) (List.map (List.drop 1) rows)
  | Nil, hr => rfl
  | Cons Nil rs, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Eq.cong (Cons (Cons y ys)) (List.rowsAreHeadsAndTails k rs hrs)

theorem List.columnsAllLength: (w: Nat) -> (rows: List (List a)) -> (h: Nat) -> List.length rows = h -> List.AllLength w rows ->
    List.AllLength h (List.transposeN w rows)
  | Zero, rows, h, hl, hr => Trivial
  | Succ k, rows, h, hl, hr =>
    Both (Eq.trans (List.headsLength k rows hr) hl)
      (List.columnsAllLength k (List.map (List.drop 1) rows) h (Eq.trans (List.lengthMap (List.drop 1) rows) hl) (List.tailsAllLength k rows hr))

theorem List.transposeNCons: (h: Nat) -> (heads: List a) -> (cols: List (List a)) -> List.length heads = h -> List.AllLength h cols ->
    List.transposeN h (Cons heads cols) = List.zipWith Cons heads (List.transposeN h cols)
  | Zero, Nil, cols, hl, hc => rfl
  | Zero, Cons x xs, cols, hl, hc => Void.exfalso (Nat.succNotZero (List.length xs) hl)
  | Succ m, Nil, cols, hl, hc => Void.exfalso (Nat.zeroNotSucc m hl)
  | Succ m, Cons x xs, cols, hl, hc =>
    Eq.cong (Cons (Cons x (List.filterMap (List.get 0) cols)))
      (List.transposeNCons m xs (List.map (List.drop 1) cols) (Nat.succInjective (List.length xs) m hl) (List.tailsAllLength m cols hc))

theorem List.transposeNTwice: (w: Nat) -> (h: Nat) -> (rows: List (List a)) -> List.length rows = h -> List.AllLength w rows ->
    List.transposeN h (List.transposeN w rows) = rows
  | Zero, h, rows, hl, hr => Eq.trans (List.transposeNNil h) (Eq.sym (List.allLengthZero rows h hl hr))
  | Succ k, h, rows, hl, hr =>
    Eq.trans
      (List.transposeNCons h (List.filterMap (List.get 0) rows) (List.transposeN k (List.map (List.drop 1) rows))
        (Eq.trans (List.headsLength k rows hr) hl)
        (List.columnsAllLength k (List.map (List.drop 1) rows) h (Eq.trans (List.lengthMap (List.drop 1) rows) hl) (List.tailsAllLength k rows hr)))
      (Eq.trans
        (Eq.cong (List.zipWith Cons (List.filterMap (List.get 0) rows))
          (List.transposeNTwice k h (List.map (List.drop 1) rows) (Eq.trans (List.lengthMap (List.drop 1) rows) hl) (List.tailsAllLength k rows hr)))
        (Eq.sym (List.rowsAreHeadsAndTails k rows hr)))

-- There are as many columns as the first row is long.
theorem List.transposeLength (rows: List (List a)): List.length (List.transpose rows) = List.length (List.headOr Nil rows) :=
  List.transposeNLength (List.length (List.headOr Nil rows)) rows

-- Transposing a rectangular list (every row the same non-zero length) twice
-- gives the list back. (With rows of length 0, the first transpose is empty
-- and the rows are lost.)
theorem List.transposeTwice (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    List.transpose (List.transpose rows) = rows
  | Nil, hr => rfl
  | Cons r rs, Both hr hrs =>
    J (y q => List.transposeN (List.length (List.headOr Nil (List.transposeN y (Cons r rs)))) (List.transposeN y (Cons r rs)) = Cons r rs)
      (List.transposeNTwice (Succ k) (List.length (List.headOr Nil (List.transposeN (Succ k) (Cons r rs)))) (Cons r rs)
        (Eq.sym (List.headsLength k (Cons r rs) (Both hr hrs))) (Both hr hrs))
      (Eq.sym hr)

-- The groups of consecutive elements that don't satisfy `p`, in order: `p`
-- marks the separators, which are dropped, and no group is empty. So
-- `List.splitBy (x => x == 0) [1, 2, 0, 0, 3]` is `[[1, 2], [3]]`.
def List.splitBy (p: a -> Bool) (xs: List a): List (List a) := List.finishGroups (List.splitGroups p xs)

-- Reads the list from the right: the group still open at the front, and the
-- groups finished after it. A right fold, so it runs as a loop over the
-- reversed list (stack-safe on long lists); `List.splitGroupsCons` is its step.
def List.splitGroups (p: a -> Bool) (xs: List a): Pair (List a) (List (List a)) :=
  List.foldRight (x st => List.splitStep x (p x) st) (MkPair Nil Nil) xs

-- Adds the element `x` in front: a separator (`True`) closes the open group,
-- anything else joins it.
def List.splitStep (x: a): Bool -> Pair (List a) (List (List a)) -> Pair (List a) (List (List a))
  | True, MkPair cur done => MkPair Nil (List.closeGroup cur done)
  | False, MkPair cur done => MkPair (Cons x cur) done

def List.finishGroups: Pair (List a) (List (List a)) -> List (List a)
  | MkPair cur done => List.closeGroup cur done

-- The step of `List.splitGroups`, which the loop form hides.
theorem List.splitGroupsCons (p: a -> Bool) (x: a) (xs: List a):
    List.splitGroups p (Cons x xs) = List.splitStep x (p x) (List.splitGroups p xs) :=
  List.foldRightCons (y st => List.splitStep y (p y) st) (MkPair Nil Nil) x xs

-- Adds a group to the finished ones, unless it is empty.
def List.closeGroup: List a -> List (List a) -> List (List a)
  | Nil, done => done
  | Cons y ys, done => Cons (Cons y ys) done

def List.splitTotal (st: Pair (List a) (List (List a))): Nat := List.length (Pair.fst st) + List.sumBy List.length (Pair.snd st)

theorem List.closeGroupSum: (cur: List a) -> (done: List (List a)) ->
    List.sumBy List.length (List.closeGroup cur done) = List.length cur + List.sumBy List.length done
  | Nil, done => rfl
  | Cons y ys, done => List.sumByCons List.length (Cons y ys) done

theorem List.splitStepTotal (x: a): (b: Bool) -> (st: Pair (List a) (List (List a))) ->
    List.splitTotal (List.splitStep x b st) + Bool.toNat b = Succ (List.splitTotal st)
  | True, MkPair cur done =>
    Eq.trans (Nat.addOne (List.sumBy List.length (List.closeGroup cur done))) (Eq.cong Succ (List.closeGroupSum cur done))
  | False, MkPair cur done => Nat.addZero (Succ (List.length cur + List.sumBy List.length done))

theorem List.splitGroupsTotal (p: a -> Bool): (xs: List a) ->
    List.splitTotal (List.splitGroups p xs) + List.occurrences p xs = List.length xs
  | Nil => rfl
  | Cons x xs =>
    rewrite List.splitGroupsCons p x xs in
      Eq.trans (Eq.sym (Nat.addAssoc (List.splitTotal (List.splitStep x (p x) (List.splitGroups p xs))) (Bool.toNat (p x)) (List.occurrences p xs)))
        (Eq.trans (Eq.cong (t => t + List.occurrences p xs) (List.splitStepTotal x (p x) (List.splitGroups p xs)))
          (Eq.cong Succ (List.splitGroupsTotal p xs)))

theorem List.finishGroupsSum: (st: Pair (List a) (List (List a))) ->
    List.sumBy List.length (List.finishGroups st) = List.splitTotal st
  | MkPair cur done => List.closeGroupSum cur done

-- The groups hold every element that isn't a separator, and nothing else.
theorem List.splitByExample: List.splitBy (x => x == 0) [1, 2, 0, 0, 3] = [[1, 2], [3]] := rfl

theorem List.splitByEdges: List.splitBy (x => x == 0) [0, 4, 0] = [[4]] := rfl

-- Splitting loses only the separators: the groups' lengths plus the number of separators is the length.
theorem List.splitByLength (p: a -> Bool) (xs: List a):
    List.sumBy List.length (List.splitBy p xs) + List.occurrences p xs = List.length xs :=
  Eq.trans (Eq.cong (t => t + List.occurrences p xs) (List.finishGroupsSum (List.splitGroups p xs))) (List.splitGroupsTotal p xs)

-- The group has no separator in it.
def List.NonSep (p: a -> Bool) (g: List a): Prop := List.all (x => !(p x)) g = True

-- Every group is non-empty and has no separator in it.
def List.Groups (p: a -> Bool): List (List a) -> Prop
  | Nil => Unit
  | Cons g gs => And (And (0 < List.length g) (List.NonSep p g)) (List.Groups p gs)

def List.SplitOk (p: a -> Bool): Pair (List a) (List (List a)) -> Prop
  | MkPair cur done => And (List.NonSep p cur) (List.Groups p done)

theorem List.closeGroupGroups (p: a -> Bool): (cur: List a) -> (done: List (List a)) -> List.NonSep p cur -> List.Groups p done ->
    List.Groups p (List.closeGroup cur done)
  | Nil, done, hc, hd => hd
  | Cons y ys, done, hc, hd => Both (Both (Nat.zeroLe (List.length ys)) hc) hd

theorem List.nonSepCons (p: a -> Bool) (x: a) (cur: List a) (h: p x = False) (hc: List.NonSep p cur): List.NonSep p (Cons x cur) :=
  rewrite h in hc

theorem List.splitStepOk (p: a -> Bool) (x: a): (b: Bool) -> p x = b -> (st: Pair (List a) (List (List a))) -> List.SplitOk p st ->
    List.SplitOk p (List.splitStep x b st)
  | True, e, MkPair cur done, Both hc hd => Both rfl (List.closeGroupGroups p cur done hc hd)
  | False, e, MkPair cur done, Both hc hd => Both (List.nonSepCons p x cur e hc) hd

theorem List.splitGroupsOk (p: a -> Bool): (xs: List a) -> List.SplitOk p (List.splitGroups p xs)
  | Nil => Both rfl Trivial
  | Cons x xs =>
    rewrite List.splitGroupsCons p x xs in List.splitStepOk p x (p x) rfl (List.splitGroups p xs) (List.splitGroupsOk p xs)

theorem List.finishGroupsOk (p: a -> Bool): (st: Pair (List a) (List (List a))) -> List.SplitOk p st -> List.Groups p (List.finishGroups st)
  | MkPair cur done, Both hc hd => List.closeGroupGroups p cur done hc hd

-- No group is empty, and none has a separator in it.
theorem List.splitByGroups (p: a -> Bool) (xs: List a): List.Groups p (List.splitBy p xs) :=
  List.finishGroupsOk p (List.splitGroups p xs) (List.splitGroupsOk p xs)

theorem List.closeGroupConcat: (cur: List a) -> (done: List (List a)) ->
    List.concat (List.closeGroup cur done) = List.append cur (List.concat done)
  | Nil, done => rfl
  | Cons y ys, done => rfl

def List.SplitKeeps (p: a -> Bool) (xs: List a) (st: Pair (List a) (List (List a))): Prop :=
  List.append (Pair.fst st) (List.concat (Pair.snd st)) = List.filter (x => !(p x)) xs

theorem List.splitStepKeeps (p: a -> Bool) (x: a) (xs: List a): (b: Bool) -> p x = b -> (st: Pair (List a) (List (List a))) ->
    List.SplitKeeps p xs st -> List.SplitKeeps p (Cons x xs) (List.splitStep x b st)
  | True, e, MkPair cur done, h =>
    Eq.trans (List.closeGroupConcat cur done)
      (Eq.trans h (Eq.sym (List.filterSkip (z => !(p z)) x xs (Eq.cong Bool.not e))))
  | False, e, MkPair cur done, h =>
    Eq.trans (Eq.cong (Cons x) h) (Eq.sym (List.filterKeep (z => !(p z)) x xs (Eq.cong Bool.not e)))

theorem List.splitGroupsKeeps (p: a -> Bool): (xs: List a) -> List.SplitKeeps p xs (List.splitGroups p xs)
  | Nil => rfl
  | Cons x xs =>
    rewrite List.splitGroupsCons p x xs in List.splitStepKeeps p x xs (p x) rfl (List.splitGroups p xs) (List.splitGroupsKeeps p xs)

theorem List.finishGroupsConcat: (st: Pair (List a) (List (List a))) ->
    List.concat (List.finishGroups st) = List.append (Pair.fst st) (List.concat (Pair.snd st))
  | MkPair cur done => List.closeGroupConcat cur done

-- Joining the groups gives back the elements that aren't separators, in order.
theorem List.splitByConcat (p: a -> Bool) (xs: List a):
    List.concat (List.splitBy p xs) = List.filter (x => !(p x)) xs :=
  Eq.trans (List.finishGroupsConcat (List.splitGroups p xs)) (List.splitGroupsKeeps p xs)

-- Only separators: no group, open or finished.
theorem List.splitGroupsSeparators (p: a -> Bool): (ys: List a) -> List.all p ys = True -> List.splitGroups p ys = MkPair Nil Nil
  | Nil, h => rfl
  | Cons y ys, h =>
    match e: p y with
      | True => rewrite List.splitGroupsCons p y ys, e, List.splitGroupsSeparators p ys h
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.splitGroupsAppendSeparators (p: a -> Bool) (ys: List a) (h: List.all p ys = True): (xs: List a) ->
    List.splitGroups p (List.append xs ys) = List.splitGroups p xs
  | Nil => List.splitGroupsSeparators p ys h
  | Cons x xs => rewrite List.splitGroupsCons p x (List.append xs ys), List.splitGroupsCons p x xs, List.splitGroupsAppendSeparators p ys h xs

-- Separators on the end change no group: `[1, 0, 0]` splits as `[1]` does.
theorem List.splitByAppendSeparators (p: a -> Bool) (xs: List a) (ys: List a) (h: List.all p ys = True):
    List.splitBy p (List.append xs ys) = List.splitBy p xs :=
  Eq.cong List.finishGroups (List.splitGroupsAppendSeparators p ys h xs)

test "List.splitBy with separators on the end" :=
  [1, 0, 2].splitBy (x => x == 0) == [[1], [2]] && [1, 0, 2, 0, 0].splitBy (x => x == 0) == [[1], [2]] && [0, 0].splitBy (x => x == 0) == Nil

-- Sums from a starting total, and one element at a time, for any `Add`:
-- the laws `zeroAdd`, `assoc` and `comm` (docs/proposals/interfaces.md §7.7).
theorem Add.addZero [auto add: Add a] (x: a): x + Add.zero = x :=
  Eq.trans (add.comm x Add.zero) (add.zeroAdd x)

theorem Add.addSwap [auto add: Add a] (w: a) (x: a) (y: a) (z: a): (w + x) + (y + z) = (w + y) + (x + z) :=
  calc (w + x) + (y + z)
    _ = w + (x + (y + z)) := add.assoc w x (y + z)
    _ = w + ((x + y) + z) := Eq.cong (t => w + t) (Eq.sym (add.assoc x y z))
    _ = w + ((y + x) + z) := Eq.cong (t => w + (t + z)) (add.comm x y)
    _ = w + (y + (x + z)) := Eq.cong (t => w + t) (add.assoc y x z)
    _ = (w + y) + (x + z) := Eq.sym (add.assoc w y (x + z))

theorem List.sumByFrom [auto add: Add b] (f: a -> b): (z: b) -> (xs: List a) -> List.foldLeft (acc x => acc + f x) z xs = z + List.sumBy f xs
  | z, Nil => Eq.sym (Add.addZero z)
  | z, Cons x xs =>
    calc List.foldLeft (acc x => acc + f x) (z + f x) xs
      _ = (z + f x) + List.sumBy f xs := List.sumByFrom f (z + f x) xs
      _ = z + (f x + List.sumBy f xs) := add.assoc z (f x) (List.sumBy f xs)
      _ = z + List.foldLeft (acc x => acc + f x) (f x) xs := Eq.cong (t => z + t) (Eq.sym (List.sumByFrom f (f x) xs))
      _ = z + List.sumBy f (Cons x xs) := Eq.cong (t => z + List.foldLeft (acc x => acc + f x) t xs) (Eq.sym (add.zeroAdd (f x)))

theorem List.sumByCons [auto add: Add b] (f: a -> b) (x: a) (xs: List a): List.sumBy f (Cons x xs) = f x + List.sumBy f xs :=
  Eq.trans (Eq.cong (t => List.foldLeft (acc x => acc + f x) t xs) (add.zeroAdd (f x))) (List.sumByFrom f (f x) xs)

theorem List.sumByAppend [auto add: Add b] (f: a -> b) (xs: List a) (ys: List a): List.sumBy f (List.append xs ys) = List.sumBy f xs + List.sumBy f ys :=
  Eq.trans (List.foldLeftAppend (acc x => acc + f x) Add.zero xs ys) (List.sumByFrom f (List.sumBy f xs) ys)

theorem List.filterKeep (p: a -> Bool) (x: a) (xs: List a) (h: p x = True): List.filter p (Cons x xs) = Cons x (List.filter p xs) :=
  J (c q => List.filterStep x (List.filter p xs) c = Cons x (List.filter p xs)) rfl (Eq.sym h)

theorem List.filterSkip (p: a -> Bool) (x: a) (xs: List a) (h: p x = False): List.filter p (Cons x xs) = List.filter p xs :=
  J (c q => List.filterStep x (List.filter p xs) c = List.filter p xs) rfl (Eq.sym h)

theorem List.foldLeftAppend (f: b -> a -> b): (z: b) -> (xs: List a) -> (ys: List a) ->
    List.foldLeft f z (List.append xs ys) = List.foldLeft f (List.foldLeft f z xs) ys
  | z, Nil, ys => rfl
  | z, Cons x xs, ys => List.foldLeftAppend f (f z x) xs ys

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.
theorem List.appendNil: (xs: List a) -> List.append xs Nil = xs
  | Nil => rfl
  | Cons x xs => Eq.cong (Cons x) (List.appendNil xs)

theorem List.appendAssoc: (xs: List a) -> (ys: List a) -> (zs: List a) -> List.append (List.append xs ys) zs = List.append xs (List.append ys zs)
  | Nil, ys, zs => rfl
  | Cons x xs, ys, zs => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
def List.occurrences (p: a -> Bool): List a -> Nat
  | Nil => 0
  | Cons x xs => Bool.toNat (p x) + List.occurrences p xs

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

-- Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate (a: Nat) (b: Nat) (c: Nat): (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

theorem List.countStep: (b: Bool) -> (k: Nat) -> (o: Nat) -> Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True, k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold (p: a -> Bool) (k: Nat): (xs: List a) ->
    List.foldLeft (n x => Nat.succIf n (p x)) k xs = k + List.occurrences p xs
  | Nil => Eq.sym (Nat.addZero k)
  | Cons x xs => Eq.trans (List.countFold p (Nat.succIf k (p x)) xs) (List.countStep (p x) k (List.occurrences p xs))

theorem List.countOccurrences (p: a -> Bool) (xs: List a): List.count p xs = List.occurrences p xs := List.countFold p 0 xs

theorem List.occurrencesSumBy (p: a -> Bool): (xs: List a) -> List.occurrences p xs = List.sumBy (x => Bool.toNat (p x)) xs
  | Nil => rfl
  | Cons x xs => rewrite List.sumByCons (x => Bool.toNat (p x)) x xs, List.occurrencesSumBy p xs

-- A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy (p: a -> Bool) (xs: List a): List.count p xs = List.sumBy (x => Bool.toNat (p x)) xs :=
  Eq.trans (List.countOccurrences p xs) (List.occurrencesSumBy p xs)

theorem List.occurrencesAppend (p: a -> Bool): (xs: List a) -> (ys: List a) ->
    List.occurrences p (List.append xs ys) = List.occurrences p xs + List.occurrences p ys
  | Nil, ys => rfl
  | Cons x xs, ys =>
    Eq.trans (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend p xs ys))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p ys)))

theorem List.countNil (p: a -> Bool): List.count p Nil = 0 := rfl

theorem List.countCons (p: a -> Bool) (x: a) (xs: List a): List.count p (Cons x xs) = Bool.toNat (p x) + List.count p xs :=
  Eq.trans (List.countOccurrences p (Cons x xs)) (Eq.cong (n => Bool.toNat (p x) + n) (Eq.sym (List.countOccurrences p xs)))

theorem List.countAppend (p: a -> Bool) (xs: List a) (ys: List a): List.count p (List.append xs ys) = List.count p xs + List.count p ys :=
  Eq.trans (List.countOccurrences p (List.append xs ys))
    (Eq.trans (List.occurrencesAppend p xs ys)
      (Eq.trans (Eq.cong (n => n + List.occurrences p ys) (Eq.sym (List.countOccurrences p xs)))
        (Eq.cong (n => List.count p xs + n) (Eq.sym (List.countOccurrences p ys)))))

theorem List.scanLeftCons (f: b -> a -> b) (z: b): (xs: List a) -> List.scanLeft f z xs = Cons z (List.drop 1 (List.scanLeft f z xs))
  | Nil => rfl
  | Cons x xs => rfl

theorem List.scanLeftAppend (f: b -> a -> b) (z: b): (xs: List a) -> (ys: List a) ->
    List.drop 1 (List.scanLeft f z (List.append xs ys)) = List.append (List.drop 1 (List.scanLeft f z xs)) (List.drop 1 (List.scanLeft f (List.foldLeft f z xs) ys))
  | Nil, ys => rfl
  | Cons x xs, ys =>
    Eq.trans (List.scanLeftCons f (f z x) (List.append xs ys))
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend f (f z x) xs ys))
        (Eq.cong (l => List.append l (List.drop 1 (List.scanLeft f (List.foldLeft f (f z x) xs) ys))) (Eq.sym (List.scanLeftCons f (f z x) xs))))

-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
def List.Perm (xs: List a) (ys: List a): Prop := (p: a -> Bool) -> List.occurrences p xs = List.occurrences p ys

theorem List.permRefl (xs: List a): List.Perm xs xs := p => rfl

theorem List.permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => Eq.sym (h p)

theorem List.permTrans (xs: List a) (ys: List a) (zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue: (xs: List a) -> List.occurrences (x => True) xs = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs: List a) (ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (x => True)) (List.occurrencesTrue ys))

-- Some element passes `p` exactly when at least one does, so permutations
-- agree on `any`.
theorem List.anyOccurrences (p: a -> Bool): (xs: List a) -> List.any p xs = Nat.leq 1 (List.occurrences p xs)
  | Nil => rfl
  | Cons x xs =>
    Bool.inspect (p x) (c => Bool.ifThenElse c (u => True) (u => List.any p xs) = Nat.leq 1 (Bool.toNat c + List.occurrences p xs))
      (t => rfl) (f => List.anyOccurrences p xs)

theorem List.anyPerm (p: a -> Bool) (xs: List a) (ys: List a) (h: List.Perm xs ys): List.any p xs = List.any p ys :=
  Eq.trans (List.anyOccurrences p xs) (Eq.trans (Eq.cong (n => Nat.leq 1 n) (h p)) (Eq.sym (List.anyOccurrences p ys)))

-- Reversing is a permutation, and keeps sums.
theorem List.occurrencesReverseOnto (p: a -> Bool): (xs: List a) -> (acc: List a) ->
    List.occurrences p (List.reverseOnto xs acc) = List.occurrences p xs + List.occurrences p acc
  | Nil, acc => rfl
  | Cons x xs, acc =>
    Eq.trans (List.occurrencesReverseOnto p xs (Cons x acc))
      (Eq.trans (Nat.addLeftComm (List.occurrences p xs) (Bool.toNat (p x)) (List.occurrences p acc))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences p xs) (List.occurrences p acc))))

theorem List.reversePerm (xs: List a): List.Perm (List.reverse xs) xs := p =>
  Eq.trans (List.occurrencesReverseOnto p xs Nil) (Nat.addZero (List.occurrences p xs))

theorem List.sumByReverseOnto (f: a -> Nat): (xs: List a) -> (acc: List a) ->
    List.sumBy f (List.reverseOnto xs acc) = List.sumBy f xs + List.sumBy f acc
  | Nil, acc => rfl
  | Cons x xs, acc =>
    Eq.trans (List.sumByReverseOnto f xs (Cons x acc))
      (Eq.trans (Eq.cong (t => List.sumBy f xs + t) (List.sumByCons f x acc))
        (Eq.trans (Nat.addLeftComm (List.sumBy f xs) (f x) (List.sumBy f acc))
          (Eq.trans (Eq.sym (Nat.addAssoc (f x) (List.sumBy f xs) (List.sumBy f acc)))
            (Eq.cong (t => t + List.sumBy f acc) (Eq.sym (List.sumByCons f x xs))))))

theorem List.sumByReverse (f: a -> Nat) (xs: List a): List.sumBy f (List.reverse xs) = List.sumBy f xs :=
  Eq.trans (List.sumByReverseOnto f xs Nil) (Nat.addZero (List.sumBy f xs))

-- Counting with a test nothing passes, and with either of two tests.
theorem List.occurrencesNone (p: a -> Bool) (h: (x: a) -> p x = False): (xs: List a) -> List.occurrences p xs = 0
  | Nil => rfl
  | Cons x xs => Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences p xs) (h x)) (List.occurrencesNone p h xs)

-- When nothing passes both `p` and `q`, the elements passing either are those
-- passing `p` plus those passing `q`.
theorem List.occurrencesOr (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = False): (xs: List a) ->
    List.occurrences (x => p x || q x) xs = List.occurrences p xs + List.occurrences q xs
  | Nil => rfl
  | Cons x xs =>
    Bool.inspect (p x)
      (c => Bool.toNat (c || q x) + List.occurrences (x => p x || q x) xs
        = (Bool.toNat c + List.occurrences p xs) + (Bool.toNat (q x) + List.occurrences q xs))
      (t => Eq.trans (Eq.cong (n => 1 + n) (List.occurrencesOr p q h xs))
        (Eq.cong (b => (1 + List.occurrences p xs) + (Bool.toNat b + List.occurrences q xs)) (Eq.sym (h x t))))
      (f => Eq.trans (Eq.cong (n => Bool.toNat (q x) + n) (List.occurrencesOr p q h xs))
        (Nat.addLeftComm (Bool.toNat (q x)) (List.occurrences p xs) (List.occurrences q xs)))

-- `s` is `xs` with some elements left out, the rest kept in order: each
-- element of `s` is matched with an element of `xs`, or `xs`'s first element
-- is skipped.
def List.Subsequence: List a -> List a -> Prop
  | Nil, ys => Unit
  | Cons x xs, Nil => Void
  | Cons x xs, Cons y ys => Or (And (x = y) (List.Subsequence xs ys)) (List.Subsequence (Cons x xs) ys)

-- Lemmas for proofs about grids: runs' lengths, `map` and `filterMap` fused,
-- `init`, `last` and `reverse` of a `map`, and transposing a grid given cell
-- by cell.
theorem List.lengthRangeFrom: (n: Nat) -> (s: Nat) -> List.length (List.rangeFrom n s) = n
  | Zero, s => rfl
  | Succ n, s => rewrite List.lengthRangeFrom n (Succ s)

theorem List.mapMap (f: b -> c) (g: a -> b): (xs: List a) -> List.map f (List.map g xs) = List.map (x => f (g x)) xs
  | Nil => rfl
  | Cons x xs => rewrite List.mapMap f g xs

theorem List.filterMapMap (f: b -> Option c) (g: a -> b): (xs: List a) -> List.filterMap f (List.map g xs) = List.filterMap (x => f (g x)) xs
  | Nil => rfl
  | Cons x xs => rewrite List.filterMapMap f g xs

theorem List.filterMapSome (f: a -> b): (xs: List a) -> List.filterMap (x => Some (f x)) xs = List.map f xs
  | Nil => rfl
  | Cons x xs => rewrite List.filterMapSome f xs

theorem List.filterMapAppend (f: a -> Option b): (xs: List a) -> (ys: List a) ->
    List.filterMap f (List.append xs ys) = List.append (List.filterMap f xs) (List.filterMap f ys)
  | Nil, ys => rfl
  | Cons x xs, ys =>
    match f x with
      | None => List.filterMapAppend f xs ys
      | Some y => rewrite List.filterMapAppend f xs ys

theorem List.initMap (f: a -> b): (xs: List a) -> List.init (List.map f xs) = List.map f (List.init xs)
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons y ys) => rewrite List.initMap f (Cons y ys)

theorem List.lastMap (f: a -> b): (xs: List a) -> List.last (List.map f xs) = Option.map f (List.last xs)
  | Nil => rfl
  | Cons x Nil => rfl
  | Cons x (Cons y ys) => List.lastMap f (Cons y ys)
theorem List.mapRangeShift (f: Nat -> b): (n: Nat) -> (s: Nat) ->
    List.map f (List.rangeFrom n (Succ s)) = List.map (i => f (Succ i)) (List.rangeFrom n s)
  | Zero, s => rfl
  | Succ n, s => rewrite List.mapRangeShift f n (Succ s)

-- Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid (cell: a -> b -> c) (rows: List a): (cols: List b) ->
    List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) rows) = List.map (y => List.map (x => cell x y) rows) cols
  | Nil => rfl
  | Cons y cols =>
    calc List.transposeN (Succ (List.length cols)) (List.map (x => List.map (cell x) (Cons y cols)) rows)
      _ = Cons (List.filterMap (List.get 0) (List.map (x => List.map (cell x) (Cons y cols)) rows))
        (List.transposeN (List.length cols) (List.map (List.drop 1) (List.map (x => List.map (cell x) (Cons y cols)) rows)))
      _ = Cons (List.filterMap (x => Some (cell x y)) rows) (List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) rows))
        := rewrite List.filterMapMap (List.get 0) (x => List.map (cell x) (Cons y cols)) rows,
          List.mapMap (List.drop 1) (x => List.map (cell x) (Cons y cols)) rows
      _ = Cons (List.map (x => cell x y) rows) (List.map (z => List.map (x => cell x z) rows) cols)
        := rewrite List.filterMapSome (x => cell x y) rows, List.transposeNGrid cell rows cols

theorem List.transposeGrid (cell: a -> b -> c) (r: a) (rows: List a) (cols: List b):
    List.transpose (List.map (x => List.map (cell x) cols) (Cons r rows)) = List.map (y => List.map (x => cell x y) (Cons r rows)) cols :=
  calc List.transpose (List.map (x => List.map (cell x) cols) (Cons r rows))
    _ = List.transposeN (List.length (List.map (cell r) cols)) (List.map (x => List.map (cell x) cols) (Cons r rows))
    _ = List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) (Cons r rows)) := rewrite List.lengthMap (cell r) cols
    _ = List.map (y => List.map (x => cell x y) (Cons r rows)) cols := List.transposeNGrid cell (Cons r rows) cols

theorem List.mapReverseOnto (f: a -> b): (xs: List a) -> (acc: List a) ->
    List.map f (List.reverseOnto xs acc) = List.reverseOnto (List.map f xs) (List.map f acc)
  | Nil, acc => rfl
  | Cons x xs, acc => List.mapReverseOnto f xs (Cons x acc)

theorem List.mapReverse (f: a -> b) (xs: List a): List.map f (List.reverse xs) = List.reverse (List.map f xs) := List.mapReverseOnto f xs Nil

-- Congruence lemmas: given callbacks that agree on every argument, a function
-- gives the same result. Their shape is fixed, since `decreasing` looks them up
-- by name (`F` + `Cong`) to follow a recursive call inside a callback
-- (docs/proposals/well-founded-recursion.md, stage 3a): `F`'s parameters in
-- order, each callback twice, then `(x…) -> f1 x… = f2 x…` for each.
theorem List.mapCong (f1: a -> b) (f2: a -> b): (xs: List a) -> ((x: a) -> f1 x = f2 x) -> List.map f1 xs = List.map f2 xs
  | Nil, ef => rfl
  | Cons x xs, ef => Eq.trans (Eq.cong (y => Cons y (List.map f1 xs)) (ef x)) (Eq.cong (ys => Cons (f2 x) ys) (List.mapCong f1 f2 xs ef))

theorem List.filterMapCong (f1: a -> Option b) (f2: a -> Option b): (xs: List a) -> ((x: a) -> f1 x = f2 x) -> List.filterMap f1 xs = List.filterMap f2 xs
  | Nil, ef => rfl
  | Cons x xs, ef => rewrite ef x, List.filterMapCong f1 f2 xs ef

theorem List.findCong (p1: a -> Bool) (p2: a -> Bool): (xs: List a) -> ((x: a) -> p1 x = p2 x) -> List.find p1 xs = List.find p2 xs
  | Nil, ep => rfl
  | Cons x xs, ep => rewrite ep x, List.findCong p1 p2 xs ep

theorem List.occurrencesCong (p1: a -> Bool) (p2: a -> Bool): (xs: List a) -> ((x: a) -> p1 x = p2 x) ->
    List.occurrences p1 xs = List.occurrences p2 xs
  | Nil, ep => rfl
  | Cons x xs, ep =>
    Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences p1 xs) (ep x))
      (Eq.cong (n => Bool.toNat (p2 x) + n) (List.occurrencesCong p1 p2 xs ep))

theorem List.foldLeftCong (f1: b -> a -> b) (f2: b -> a -> b): (z: b) -> (xs: List a) -> ((acc: b) -> (x: a) -> f1 acc x = f2 acc x) ->
    List.foldLeft f1 z xs = List.foldLeft f2 z xs
  | z, Nil, ef => rfl
  | z, Cons x xs, ef => Eq.trans (Eq.cong (t => List.foldLeft f1 t xs) (ef z x)) (List.foldLeftCong f1 f2 (f2 z x) xs ef)

theorem List.sumByCong [auto add: Add b] (f1: a -> b) (f2: a -> b) (xs: List a) (ef: (x: a) -> f1 x = f2 x): List.sumBy f1 xs = List.sumBy f2 xs :=
  List.foldLeftCong (acc x => acc + f1 x) (acc x => acc + f2 x) Add.zero xs (acc x => Eq.cong (t => acc + t) (ef x))

theorem Option.flatMapMap (g: b -> Option c) (f: a -> b): (m: Option a) -> Option.flatMap g (Option.map f m) = Option.flatMap (x => g (f x)) m
  | None => rfl
  | Some x => rfl

theorem List.lengthZipWith3 (f: a -> b -> c -> e): (xs: List a) -> (ys: List b) -> (zs: List c) ->
    List.length ys = List.length xs -> List.length zs = List.length xs -> List.length (List.zipWith3 f xs ys zs) = List.length xs
  | Nil, ys, zs, h1, h2 => rfl
  | Cons x xs, Nil, zs, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

-- A sum over a list is the sum over its indices.

-- `x` is an element of the list.
def List.Mem (x: a) (xs: List a): Prop := List.Any (y => y = x) xs

-- No element of the first list is in the second.
def List.Disjoint (xs: List a) (ys: List a): Prop := List.All (x => Not (List.Mem x ys)) xs

-- No element occurs twice.
def List.Distinct: List a -> Prop
  | Nil => Unit
  | Cons x xs => And (Not (List.Mem x xs)) (List.Distinct xs)

theorem List.distinctNil: List.Distinct (Nil: List a) := Trivial

theorem List.distinctCons (x: a) (xs: List a) (h: Not (List.Mem x xs)) (d: List.Distinct xs): List.Distinct (Cons x xs) := Both h d

-- An element of two lists joined is in one of them.
theorem List.memAppend (x: a): (xs: List a) -> (ys: List a) -> List.Mem x (List.append xs ys) -> Or (List.Mem x xs) (List.Mem x ys)
  | Nil, ys, h => Inr h
  | Cons z zs, ys, Inl h => Inl (Inl h)
  | Cons z zs, ys, Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- `f x` is in `List.map f xs` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective (f: a -> b) (inj: (x: a) -> (y: a) -> f x = f y -> x = y) (x: a): (xs: List a) -> List.Mem (f x) (List.map f xs) -> List.Mem x xs
  | Nil, h => h
  | Cons z zs, Inl h => Inl (inj z x h)
  | Cons z zs, Inr h => Inr (List.memMapInjective f inj x zs h)

-- If `x` is in `xs`, `f x` is in `List.map f xs`.
theorem List.memMap (f: a -> b) (x: a): (xs: List a) -> List.Mem x xs -> List.Mem (f x) (List.map f xs)
  | Nil, h => h
  | Cons z zs, Inl h => Inl (Eq.cong f h)
  | Cons z zs, Inr h => Inr (List.memMap f x zs h)

-- Use "some element satisfies `p`": take that element, know it is in the
-- list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim (p: a -> Prop) (goal: Prop): (xs: List a) -> List.Any p xs -> ((x: a) -> List.Mem x xs -> p x -> goal) -> goal
  | Nil, h, k => Void.exfalso h
  | Cons z zs, Inl h, k => k z (Inl rfl) h
  | Cons z zs, Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

-- What is in `List.map f xs` is `f x` for some `x` in `xs` (said with
-- `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny (f: a -> b) (y: b): (xs: List a) -> List.Mem y (List.map f xs) -> List.Any (x => f x = y) xs
  | Nil, h => h
  | Cons z zs, Inl h => Inl h
  | Cons z zs, Inr h => Inr (List.memMapAny f y zs h)

-- What `List.filter p` keeps was in the list, and passes `p`.
theorem List.memFilter (p: a -> Bool) (x: a): (xs: List a) -> List.Mem x (List.filter p xs) -> And (List.Mem x xs) (p x = True)
  | Nil, h => Void.exfalso h
  | Cons y ys, h =>
    match e: p y with
      | True =>
        match h with
          | Inl q => Both (Inl q) (rewrite q at e)
          | Inr m =>
            match List.memFilter p x ys m with
              | Both inYs px => Both (Inr inYs) px
      | False =>
        match List.memFilter p x ys h with
          | Both inYs px => Both (Inr inYs) px

-- The run `List.rangeFrom c s` holds the numbers from `s` up to, not
-- including, `s + c`.
theorem List.memRangeFrom (x: Nat): (c: Nat) -> (s: Nat) -> List.Mem x (List.rangeFrom c s) -> And (s <= x) (x < s + c)
  | Zero, s, h => Void.exfalso h
  | Succ c, s, Inl q => rewrite <- q in Both (Nat.leRefl s) (Nat.ltAddSuccSelf s c)
  | Succ c, s, Inr m =>
    match List.memRangeFrom x c (Succ s) m with
      | Both lo hi => Both (Nat.lessLe s x lo) (Nat.ltAddSucc s c x hi)

-- `List.between lo hi` holds the numbers from `lo` to `hi`, both included.
-- The numbers are implicit, for use on a `List.Member`'s `isIn`.
theorem List.memBetween [x lo hi: Nat] (h: List.Mem x (List.between lo hi)): And (lo <= x) (x <= hi) :=
  match List.memRangeFrom x (hi + 1 - lo) lo h with
    | Both above below => Both above (Nat.ltCongRight x (hi + 1) (Succ hi) (Nat.addOne hi) (Nat.ltOfRunSub lo x (hi + 1) above below))

-- The other way: every number from `s` up to, not including, `s + c` is in
-- the run `List.rangeFrom c s`.
theorem List.memRangeFromIntro (x: Nat): (c: Nat) -> (s: Nat) -> s <= x -> x < s + c -> List.Mem x (List.rangeFrom c s)
  | Zero, s, lo, hi => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) s x (Nat.ltCongRight x (s + 0) s (Nat.addZero s) hi) lo))
  | Succ c, s, lo, hi =>
    match e: Nat.leq (Succ s) x with
      | True => Inr (List.memRangeFromIntro x c (Succ s) e (Nat.ltSuccAdd s c x hi))
      | False => Inl (Nat.leAntisym s x lo (Nat.leqFalse (Succ s) x e))

-- And for `List.between lo hi`: every number from `lo` to `hi`, both included.
theorem List.memBetweenIntro (x: Nat) (lo: Nat) (hi: Nat) (above: lo <= x) (below: x <= hi): List.Mem x (List.between lo hi) :=
  List.memRangeFromIntro x (hi + 1 - lo) lo above
    (Nat.ltCongRight x (hi + 1) (lo + (hi + 1 - lo))
      (Eq.sym (Nat.addSubCancel lo (hi + 1) (Nat.leTrans lo x (hi + 1) above (Nat.leTrans x hi (hi + 1) below (Nat.leCongRight hi (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leSucc hi))))))
      (Nat.ltCongRight x (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leLessSucc x hi below)))

-- A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro (f: a -> List b) (x: a) (y: b): (xs: List a) -> List.Mem x xs -> List.Mem y (f x) -> List.Mem y (List.flatMap xs f)
  | Nil, h, m => Void.exfalso h
  | Cons z zs, Inl h, m => List.anyAppendLeft (w => w = y) (f z) (List.concat (List.map f zs)) (rewrite h in m)
  | Cons z zs, Inr h, m => List.anyAppendRight (w => w = y) (f z) (List.concat (List.map f zs)) (List.memFlatMapIntro f x y zs h m)

-- And back: what is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim (f: a -> List b) (y: b): (xs: List a) -> List.Mem y (List.flatMap xs f) -> List.Any (x => List.Mem y (f x)) xs
  | Nil, h => h
  | Cons z zs, h =>
    match List.memAppend y (f z) (List.concat (List.map f zs)) h with
      | Inl m => Inl m
      | Inr m => Inr (List.memFlatMapElim f y zs m)

-- Mapping an injective function keeps a list distinct.
theorem List.distinctMap (f: a -> b) (inj: (x: a) -> (y: a) -> f x = f y -> x = y): (xs: List a) -> List.Distinct xs -> List.Distinct (List.map f xs)
  | Nil, d => Trivial
  | Cons x xs, Both h d => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap f inj xs d)

-- Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend: (xs: List a) -> (ys: List a) -> List.Distinct xs -> List.Distinct ys -> List.Disjoint xs ys -> List.Distinct (List.append xs ys)
  | Nil, ys, dx, dy, dj => dy
  | Cons x xs, ys, Both hx dx, dy, Both hj dj =>
    Both
      (m => match List.memAppend x xs ys m with
        | Inl inXs => hx inXs
        | Inr inYs => hj inYs)
      (List.distinctAppend xs ys dx dy dj)

-- The same head in front of two lists gives the same list only if the tails
-- were the same.
theorem List.consInjective (x: a) (ys: List a) (zs: List a) (p: Cons x ys = Cons x zs): ys = zs := Eq.cong (List.drop 1) p

-- A list starting with x isn't among lists that all start with y, a
-- different element.
theorem List.notMemMapCons (x: a) (y: a) (ne: Not (x = y)) (xs: List a): (ys: List (List a)) -> Not (List.Mem (Cons x xs) (List.map (Cons y) ys))
  | Nil, m => m
  | Cons z zs, Inl p => ne (Eq.sym (Eq.cong (List.headOr x) p))
  | Cons z zs, Inr q => List.notMemMapCons x y ne xs zs q

-- Lists that all start with x and lists that all start with a different y
-- have none in common.
theorem List.disjointMapCons (x: a) (y: a) (ne: Not (x = y)) (ys: List (List a)): (xs: List (List a)) ->
    List.Disjoint (List.map (Cons x) xs) (List.map (Cons y) ys)
  | Nil => Trivial
  | Cons z zs => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons x y ne ys zs)

-- A run of numbers has no repeats.
theorem List.distinctRangeFrom: (c: Nat) -> (s: Nat) -> List.Distinct (List.rangeFrom c s)
  | Zero, s => Trivial
  | Succ c, s =>
    Both (m => match List.memRangeFrom s c (Succ s) m with
        | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

theorem List.distinctBetween (lo: Nat) (hi: Nat): List.Distinct (List.between lo hi) := List.distinctRangeFrom (hi + 1 - lo) lo

-- Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem (p: a -> Prop): (xs: List a) -> ((x: a) -> List.Mem x xs -> p x) -> List.All p xs
  | Nil, h => Trivial
  | Cons z zs, h => Both (h z (Inl rfl)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

-- A `flatMap` of distinct lists has no repeats if the list mapped over has none
-- and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap (f: a -> List b) (key: b -> a): (xs: List a) -> List.Distinct xs ->
    ((x: a) -> List.Mem x xs -> List.Distinct (f x)) ->
    ((x: a) -> List.Mem x xs -> (y: b) -> List.Mem y (f x) -> key y = x) ->
    List.Distinct (List.flatMap xs f)
  | Nil, d, distinctEach, keyed => Trivial
  | Cons x xs, Both notLater later, distinctEach, keyed =>
    List.distinctAppend (f x) (List.flatMap xs f)
      (distinctEach x (Inl rfl))
      (List.distinctFlatMap f key xs later (z inXs => distinctEach z (Inr inXs)) (z inXs => keyed z (Inr inXs)))
      -- Nothing in `f x` is in a later `f z`: it would have key `x` and key `z`.
      (List.allOfMem (y => Not (List.Mem y (List.flatMap xs f))) (f x) (y fromX inLater =>
        List.anyElim (z => List.Mem y (f z)) Void xs (List.memFlatMapElim f y xs inLater)
          (z inXs fromZ =>
            notLater (rewrite Eq.trans (Eq.sym (keyed x (Inl rfl) y fromX)) (keyed z (Inr inXs) y fromZ) in inXs))))

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v)
    (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map Succ [1, 2]) :=
  List.distinctMap Succ (x y p => Nat.succInjective x y p) [1, 2] List.distinctExample

theorem List.consInjectiveExample (ys: List Nat) (zs: List Nat) (p: Cons 1 ys = Cons 1 zs): ys = zs := List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map (Cons 0) [[1], [2]]) (List.map (Cons 1) [[1], Nil]) :=
  List.disjointMapCons 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [[1], Nil] [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map (Cons 0) [Nil]) (List.map (Cons 1) [Nil])) :=
  List.distinctAppend (List.map (Cons 0) [Nil]) (List.map (Cons 1) [Nil])
    (List.distinctMap (Cons 0) (List.consInjective 0) [Nil] (Both (m => m) Trivial))
    (List.distinctMap (Cons 1) (List.consInjective 1) [Nil] (Both (m => m) Trivial))
    (List.disjointMapCons 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [Nil] [Nil])

theorem List.memBetweenIntroExample: List.Mem 3 (List.between 1 5) := List.memBetweenIntro 3 1 5 rfl rfl

theorem List.memFlatMapExample: List.Mem 20 (List.flatMap [1, 2] (x => [x, x * 10])) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl rfl)) (Inr (Inl rfl))

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend [1] [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v) Trivial)

-- What `List.All` says of an element of the list.
theorem List.allMem (p: a -> Prop) (x: a): (xs: List a) -> List.All p xs -> List.Mem x xs -> p x
  | Nil, h, m => Void.exfalso m
  | Cons z zs, Both pz h, Inl e => rewrite <- e in pz
  | Cons z zs, Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

-- What `List.find` finds passes the test and is in the list.
theorem List.findSome (p: a -> Bool): (xs: List a) -> (y: a) -> List.find p xs = Some y -> And (p y = True) (List.Mem y xs)
  | Nil, y, h => Void.exfalso (Option.noneNotSome y h)
  | Cons x xs, y, h =>
    match e: p x with
      | True => Both (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective x y h))) e) (Inl (Option.someInjective x y h))
      | False =>
        match List.findSome p xs y h with
          | Both py m => Both py (Inr m)

-- `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem (p: a -> Bool) (x: a) (px: p x = True): (xs: List a) -> List.Mem x xs -> List.find p xs = None -> Void
  | Nil, m, h => m
  | Cons z zs, Inl e, h => Option.someNotNone x (rewrite e, px at h)
  | Cons z zs, Inr m, h =>
    match c: p z with
      | True => Option.someNotNone z h
      | False => List.findNoneNotMem p x px zs m h

-- An element that passes makes `List.any` true.
theorem List.anyOfMem (q: a -> Bool) (y: a) (qy: q y = True): (xs: List a) -> List.Mem y xs -> List.any q xs = True
  | Nil, m => Void.exfalso m
  | Cons x xs, Inl e => rewrite e, qy in rfl
  | Cons x xs, Inr m =>
    match c: q x with
      | True => rfl
      | False => List.anyOfMem q y qy xs m

-- And back: when `List.any` is true, some element of the list passes.
theorem List.anyTrueElim (p: a -> Bool) (goal: Prop): (xs: List a) -> List.any p xs = True -> ((x: a) -> List.Mem x xs -> p x = True -> goal) -> goal
  | Nil, h, k => Void.exfalso (Bool.falseNotTrue h)
  | Cons z zs, h, k =>
    match c: p z with
      | True => k z (Inl rfl) c
      | False => List.anyTrueElim p goal zs h (x inZs px => k x (Inr inZs) px)

-- What `List.find p` finds passes any other test some element passes.
theorem List.findAny (p: a -> Bool) (q: a -> Bool) (xs: List a) (y: a) (qy: q y = True) (h: List.find p xs = Some y): List.any q xs = True :=
  match List.findSome p xs y h with
    | Both py m => List.anyOfMem q y qy xs m

-- A key of part of the list is a key of the list.
theorem List.memMapOfSub (key: a -> k) (s: List a) (xs: List a) (sub: (y: a) -> List.Mem y s -> List.Mem y xs) (z: k)
    (m: List.Mem z (List.map key s)): List.Mem z (List.map key xs) :=
  List.anyElim (y => key y = z) (List.Mem z (List.map key xs)) s (List.memMapAny key z s m)
    (y inS e => rewrite <- e in List.memMap key y xs (sub y inS))

-- Keeping some elements keeps their keys distinct.
theorem List.distinctMapFilter (key: a -> k) (p: a -> Bool): (xs: List a) -> List.Distinct (List.map key xs) ->
    List.Distinct (List.map key (List.filter p xs))
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: p x with
      | True =>
        Both
          (m => notMem (List.memMapOfSub key (List.filter p xs) xs (y inFiltered => match List.memFilter p y xs inFiltered with
            | Both inXs py => inXs) (key x) m))
          (List.distinctMapFilter key p xs d)
      | False => List.distinctMapFilter key p xs d

-- A key of a `filterMap`'s result is the key of an element it came from,
-- when each result has the key of its element.
theorem List.memMapFilterMap (f: a -> Option b) (ka: a -> k) (kb: b -> k) (hk: (x: a) -> (y: b) -> f x = Some y -> kb y = ka x) (z: k):
    (xs: List a) -> List.Mem z (List.map kb (List.filterMap f xs)) -> List.Mem z (List.map ka xs)
  | Nil, m => m
  | Cons x xs, m =>
    match e: f x with
      | None => Inr (List.memMapFilterMap f ka kb hk z xs m)
      | Some y =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (hk x y e)) q)
          | Inr r => Inr (List.memMapFilterMap f ka kb hk z xs r)

-- So `filterMap` keeps keys distinct.
theorem List.distinctMapFilterMap (f: a -> Option b) (ka: a -> k) (kb: b -> k) (hk: (x: a) -> (y: b) -> f x = Some y -> kb y = ka x):
    (xs: List a) -> List.Distinct (List.map ka xs) -> List.Distinct (List.map kb (List.filterMap f xs))
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: f x with
      | None => List.distinctMapFilterMap f ka kb hk xs d
      | Some y =>
        Both (m => notMem (rewrite <- hk x y e in List.memMapFilterMap f ka kb hk (kb y) xs m))
          (List.distinctMapFilterMap f ka kb hk xs d)

-- Two lists with distinct keys and no key in common, joined, have distinct keys.
theorem List.distinctMapAppend (key: a -> k) (xs: List a) (ys: List a) (dx: List.Distinct (List.map key xs)) (dy: List.Distinct (List.map key ys))
    (dj: List.Disjoint (List.map key xs) (List.map key ys)): List.Distinct (List.map key (List.append xs ys)) :=
  rewrite List.mapAppend key xs ys in List.distinctAppend (List.map key xs) (List.map key ys) dx dy dj

theorem List.distinctMapFilterExample: List.Distinct (List.map Succ (List.filter (x => Nat.leq 2 x) [1, 2])) :=
  List.distinctMapFilter Succ (x => Nat.leq 2 x) [1, 2] List.distinctMapExample

-- Mapping with a state threaded left to right (Haskell's `mapAccumL`).
-- `xs` is the main value: `xs.mapAccumLeft 0 (s x => MkPair (s + x) (s * x))`.
-- The function takes the state and an element and gives the next state and
-- the mapped element; the result is the final state and the mapped list.
-- A loop: `done` holds the mapped elements so far, newest first.
def List.mapAccumLeftGo (f: s -> a -> Pair s b) (state: s) (done: List b): List a -> Pair s (List b)
  | Nil => MkPair state (List.reverseOnto done Nil)
  | Cons x xs =>
    let next := f state x
    List.mapAccumLeftGo f (Pair.fst next) (Cons (Pair.snd next) done) xs

def List.mapAccumLeft (xs: List a) (initial: s) (f: s -> a -> Pair s b): Pair s (List b) := List.mapAccumLeftGo f initial Nil xs

-- Splits a list of pairs into the list of firsts and the list of seconds.
def List.unzip (ps: List (Pair a b)): Pair (List a) (List b) := MkPair (List.map Pair.fst ps) (List.map Pair.snd ps)

-- Dropping elements never makes a list longer.
theorem List.lengthDropLe: (n: Nat) -> (xs: List a) -> List.length (List.drop n xs) <= List.length xs
  | Zero, xs => Nat.leRefl (List.length xs)
  | Succ n, Nil => rfl
  | Succ n, Cons x xs => Nat.leTrans (List.length (List.drop n xs)) (List.length xs) (Succ (List.length xs)) (List.lengthDropLe n xs) (Nat.leSucc (List.length xs))

-- Dropping at least one element of a non-empty list leaves a shorter list.
theorem List.dropConsLess: (n: Nat) -> (x: a) -> (xs: List a) -> n != 0 -> List.length (List.drop n (Cons x xs)) < List.length (Cons x xs)
  | Zero, x, xs, h => Void.exfalso (h rfl)
  | Succ n, x, xs, h => Nat.leLessSucc (List.length (List.drop n xs)) (List.length xs) (List.lengthDropLe n xs)

-- Chunks of `n` elements, in order; the last chunk is shorter when `n` doesn't
-- divide the length. `n = 0` is no sensible chunk size, so it gives the whole
-- list as one chunk (`[xs]`, or `[]` for an empty `xs`).
def List.chunksOfPositive (n: Nat) (xs: List a) [auto pos: n != 0]: List (List a)
    decreasing List.length xs
:=
  match xs with
    | Nil => Nil
    | Cons y ys => Cons (List.take n (Cons y ys)) (List.chunksOfPositive n (List.drop n (Cons y ys)) [decreasing := List.dropConsLess n y ys pos])

-- `xs` is the main value: `xs.chunksOf 2`. `[1, 2, 3].chunksOf 2` is
-- `[[1, 2], [3]]`.
def List.chunksOf (xs: List a) (n: Nat): List (List a) :=
  match n with
    | Zero => match xs with
      | Nil => Nil
      | Cons y ys => Cons (Cons y ys) Nil
    | Succ k => List.chunksOfPositive (Succ k) xs

-- The elements without repeats, keeping the first occurrence of each and the
-- order. `seen` is what came before. Needs `DecEq`; quadratic.
def List.distinctFrom [auto eq: DecEq a] (seen: List a): List a -> List a
  | Nil => Nil
  | Cons x xs => if List.any (y => y == x) seen then List.distinctFrom seen xs else Cons x (List.distinctFrom (Cons x seen) xs)

-- `xs` is the main value: `xs.distinct`. `[3, 1, 3, 2, 1].distinct` is `[3, 1, 2]`.
def List.distinct [auto eq: DecEq a] (xs: List a): List a := List.distinctFrom Nil xs

test "List.mapAccumLeft" := [1, 2, 3].mapAccumLeft 0 (s x => MkPair (s + x) (s * x)) == MkPair 6 [0, 2, 9]
test "List.mapAccumLeft empty" := (Nil: List Nat).mapAccumLeft 7 (s x => MkPair (s + x) x) == MkPair 7 Nil
test "List.unzip" := List.unzip [MkPair 1 True, MkPair 2 False] == MkPair [1, 2] [True, False]
test "List.unzip empty" := List.unzip (Nil: List (Pair Nat Nat)) == MkPair Nil Nil
test "List.chunksOf" := List.chunksOf [1, 2, 3, 4, 5] 2 == [[1, 2], [3, 4], [5]]
test "List.chunksOf exact" := List.chunksOf [1, 2, 3, 4] 2 == [[1, 2], [3, 4]]
test "List.chunksOf bigger than the list" := List.chunksOf [1, 2] 5 == [[1, 2]]
test "List.chunksOf empty" := List.chunksOf (Nil: List Nat) 3 == Nil
test "List.chunksOf zero is one chunk" := List.chunksOf [1, 2, 3] 0 == [[1, 2, 3]] && List.chunksOf (Nil: List Nat) 0 == Nil
test "List.distinct" := [3, 1, 3, 2, 1].distinct == [3, 1, 2]
test "List.distinct empty" := (Nil: List Nat).distinct == Nil
-- Second batch (SW-235). The main value comes first, the function last.

-- The element with the largest key, or `None` for an empty list. When several
-- keys are largest, the FIRST of those elements wins: `[(1, "a"), (3, "b"),
-- (3, "c")].maxBy Pair.fst` is `Some (3, "b")`. (Haskell's `maximumBy` and
-- Clojure's `max-key` return the last one, so a port must not assume they agree.)
def List.maxByStep [auto ord: Ord b] (f: a -> b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Less => x
  | _ => best

def List.maxBy [auto ord: Ord b] (xs: List a) (f: a -> b): Option a :=
  match xs with
    | Nil => None
    | Cons x ys => Some (List.foldLeft (best y => List.maxByStep f best y) x ys)

-- The element with the smallest key; on a tie the FIRST one wins, as for
-- `List.maxBy`.
def List.minByStep [auto ord: Ord b] (f: a -> b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Greater => x
  | _ => best

def List.minBy [auto ord: Ord b] (xs: List a) (f: a -> b): Option a :=
  match xs with
    | Nil => None
    | Cons x ys => Some (List.foldLeft (best y => List.minByStep f best y) x ys)

-- The longest prefix of elements satisfying `p`.
def List.takeWhile (xs: List a) (p: a -> Bool): List a :=
  match xs with
    | Nil => Nil
    | Cons x ys => if p x then Cons x (List.takeWhile ys p) else Nil

-- What is left after `List.takeWhile`: from the first element not satisfying `p`.
def List.dropWhile (xs: List a) (p: a -> Bool): List a :=
  match xs with
    | Nil => Nil
    | Cons x ys => if p x then List.dropWhile ys p else Cons x ys

-- `List.takeWhile` and `List.dropWhile` together.
def List.span (xs: List a) (p: a -> Bool): Pair (List a) (List a) := MkPair (List.takeWhile xs p) (List.dropWhile xs p)

-- The first `n` elements and the rest: `xs.splitAt 2` is `(xs.take 2, xs.drop 2)`.
def List.splitAt (xs: List a) (n: Nat): Pair (List a) (List a) := MkPair (List.take n xs) (List.drop n xs)

-- Without the last `n` elements (all of them if there are fewer).
def List.dropRight (xs: List a) (n: Nat): List a := List.take (List.length xs - n) xs

-- Every suffix, longest first, ending with the empty list:
-- `[1, 2].tails` is `[[1, 2], [2], []]`.
def List.tails: List a -> List (List a)
  | Nil => Cons Nil Nil
  | Cons x xs => Cons (Cons x xs) (List.tails xs)

-- The index of the first element satisfying `p`.
def List.findIndexFrom (i: Nat) (p: a -> Bool): List a -> Option Nat
  | Nil => None
  | Cons x xs => if p x then Some i else List.findIndexFrom (Succ i) p xs

def List.findIndex (xs: List a) (p: a -> Bool): Option Nat := List.findIndexFrom 0 p xs

-- Each element with its index from `i`.
def List.withIndexFrom (i: Nat): List a -> List (Pair Nat a)
  | Nil => Nil
  | Cons x xs => Cons (MkPair i x) (List.withIndexFrom (Succ i) xs)

-- Pairs each element with its position, counting from 0, the position first
-- (Rust's `enumerate`): `["a", "b"].withIndex` is `[(0, "a"), (1, "b")]`.
def List.withIndex (xs: List a): List (Pair Nat a) := List.withIndexFrom 0 xs

-- The first `Some` that `f` gives (Lean's `findSome?`, Scala's `collectFirst`).
def List.findMap (xs: List a) (f: a -> Option b): Option b :=
  match xs with
    | Nil => None
    | Cons x ys => Option.orElse (f x) (List.findMap ys f)

-- `findMap` is the first of the `filterMap` results, found without building
-- the rest.
theorem List.findMapIsHeadFilterMap (f: a -> Option b): (xs: List a) -> List.findMap xs f = List.head (List.filterMap f xs)
  | Nil => rfl
  | Cons x xs =>
    match f x with
      | None => List.findMapIsHeadFilterMap f xs
      | Some y => rfl

-- Maps, then joins: `xs.flatMap f` is `List.concat (List.map f xs)`.
def List.flatMap (xs: List a) (f: a -> List b): List b := List.concat (List.map f xs)

-- Every pair, the first elements in order and the second elements within
-- each: `[1, 2].cross ["a", "b"]` is `[(1, "a"), (1, "b"), (2, "a"), (2, "b")]`.
def List.cross (xs: List a) (ys: List b): List (Pair a b) := List.flatMap xs (x => List.map (y => MkPair x y) ys)

-- Every element with each later one, in order: `[1, 2, 3].pairs` is
-- `[(1, 2), (1, 3), (2, 3)]`. A list of n elements has n(n - 1)/2 of them.
def List.pairs: List a -> List (Pair a a)
  | Nil => Nil
  | Cons x xs => List.append (List.map (y => MkPair x y) xs) (List.pairs xs)

theorem List.lengthTails: (xs: List a) -> List.length (List.tails xs) = Succ (List.length xs)
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take n xs := rfl

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := rfl

test "List.maxBy" := [MkPair 2 "bb", MkPair 1 "a", MkPair 3 "ccc"].maxBy Pair.fst == Some (MkPair 3 "ccc") && (Nil: List Nat).maxBy (x => x) == None
test "List.maxBy first wins a tie" := [MkPair 1 "a", MkPair 3 "b", MkPair 3 "c"].maxBy Pair.fst == Some (MkPair 3 "b")
test "List.minBy first wins a tie" := [MkPair 3 "z", MkPair 1 "a", MkPair 1 "b"].minBy Pair.fst == Some (MkPair 1 "a") && (Nil: List Nat).minBy (x => x) == None
test "List.takeWhile and dropWhile" := [1, 2, 5, 1].takeWhile (x => Nat.leq x 2) == [1, 2] && [1, 2, 5, 1].dropWhile (x => Nat.leq x 2) == [5, 1]
test "List.takeWhile all and none" := [1, 2].takeWhile (x => Nat.leq x 8) == [1, 2] && [1, 2].dropWhile (x => Nat.leq x 8) == Nil && [4].takeWhile (x => Nat.leq x 2) == Nil
test "List.span" := List.span [1, 2, 5, 1] (x => Nat.leq x 2) == MkPair [1, 2] [5, 1] && List.span (Nil: List Nat) (x => Nat.leq x 2) == MkPair Nil Nil
test "List.span dot" := [1, 2, 5, 1].span (x => Nat.leq x 2) == MkPair [1, 2] [5, 1]
test "List.splitAt" := [1, 2, 3].splitAt 1 == MkPair [1] [2, 3] && [1, 2].splitAt 5 == MkPair [1, 2] Nil && [1, 2].splitAt 0 == MkPair Nil [1, 2]
test "List.dropRight" := [1, 2, 3, 4].dropRight 1 == [1, 2, 3] && [1, 2].dropRight 5 == Nil && [1, 2].dropRight 0 == [1, 2]
test "List.tails" := [1, 2].tails == [[1, 2], [2], Nil] && (Nil: List Nat).tails == [Nil]
test "List.findIndex" := [5, 6, 7].findIndex (x => Nat.leq 6 x) == Some 1 && [5].findIndex (x => Nat.leq 10 x) == None
test "List.withIndex" := ["a", "b"].withIndex == [MkPair 0 "a", MkPair 1 "b"] && (Nil: List Nat).withIndex == Nil
test "List.findMap" := [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == Some 30 && [1].findMap (x => (None: Option Nat)) == None
test "List.findMap is the head of filterMap" :=
  [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == ([1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 10) else None)).head &&
    [1].findMap (x => (None: Option Nat)) == ([1].filterMap (x => (None: Option Nat))).head
test "List.between" := List.between 2 5 == [2, 3, 4, 5] && List.between 3 3 == [3] && List.between 4 2 == Nil && List.between 0 1 == [0, 1]
test "List.flatMap" := [1, 2, 3].flatMap (x => List.replicate x x) == [1, 2, 2, 3, 3, 3]
test "List.pairs" := [1, 2, 3].pairs == [MkPair 1 2, MkPair 1 3, MkPair 2 3] && (Nil: List Nat).pairs == Nil && [1].pairs == (Nil: List (Pair Nat Nat))
test "List.pairs count" := List.length (List.range 10).pairs == 45
test "List.cross" := [1, 2].cross ["a", "b"] == [MkPair 1 "a", MkPair 1 "b", MkPair 2 "a", MkPair 2 "b"] && [1].cross (Nil: List Nat) == Nil

-- `map` through the other list functions (SW-198, day 8).

theorem List.mapAppend (f: a -> b): (xs: List a) -> (ys: List a) -> List.map f (List.append xs ys) = List.append (List.map f xs) (List.map f ys)
  | Nil, ys => rfl
  | Cons x xs, ys => rewrite List.mapAppend f xs ys

theorem List.takeMap (f: a -> b): (k: Nat) -> (xs: List a) -> List.take k (List.map f xs) = List.map f (List.take k xs)
  | Zero, xs => rfl
  | Succ k, Nil => rfl
  | Succ k, Cons x xs => rewrite List.takeMap f k xs

theorem List.foldLeftMap (f: c -> b -> c) (g: a -> b): (z: c) -> (xs: List a) ->
    List.foldLeft f z (List.map g xs) = List.foldLeft (acc x => f acc (g x)) z xs
  | z, Nil => rfl
  | z, Cons x xs => List.foldLeftMap f g (f z (g x)) xs

theorem List.anyMap (p: b -> Bool) (f: a -> b): (xs: List a) -> List.any p (List.map f xs) = List.any (x => p (f x)) xs
  | Nil => rfl
  | Cons x xs => rewrite List.anyMap p f xs

theorem List.countMap (p: b -> Bool) (f: a -> b) (xs: List a): List.count p (List.map f xs) = List.count (x => p (f x)) xs :=
  List.foldLeftMap (n x => Nat.succIf n (p x)) f 0 xs

-- The first k numbers of a longer run.
theorem List.takeRangeFrom: (k: Nat) -> (n: Nat) -> (s: Nat) -> k <= n -> List.take k (List.rangeFrom n s) = List.rangeFrom k s
  | Zero, n, s, h => rfl
  | Succ k, Zero, s, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Succ n, s, h => rewrite List.takeRangeFrom k n (Succ s) h

-- The pairs of a mapped list are the list's pairs, mapped.
theorem List.pairsMap (f: a -> b): (xs: List a) -> List.pairs (List.map f xs) = List.map (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (List.pairs xs)
  | Nil => rfl
  | Cons x xs =>
    rewrite List.mapAppend (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (List.map (y => MkPair x y) xs) (List.pairs xs),
      List.mapMap (y => MkPair (f x) y) f xs, List.mapMap (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (y => MkPair x y) xs,
      List.pairsMap f xs

-- Callbacks that agree on the list's elements (not everywhere, as for
-- `List.mapCong`) give the same result.
theorem List.mapCongMem (f1: a -> b) (f2: a -> b): (xs: List a) -> ((x: a) -> (m: List.Mem x xs) -> f1 x = f2 x) -> List.map f1 xs = List.map f2 xs
  | Nil, ef => rfl
  | Cons x xs, ef => rewrite ef x (Inl rfl), List.mapCongMem f1 f2 xs (y m => ef y (Inr m))

theorem List.filterCongMem (p1: a -> Bool) (p2: a -> Bool): (xs: List a) -> ((x: a) -> (m: List.Mem x xs) -> p1 x = p2 x) -> List.filter p1 xs = List.filter p2 xs
  | Nil, ep => rfl
  | Cons x xs, ep => rewrite ep x (Inl rfl), List.filterCongMem p1 p2 xs (y m => ep y (Inr m))

theorem List.anyCongMem (p1: a -> Bool) (p2: a -> Bool): (xs: List a) -> ((x: a) -> (m: List.Mem x xs) -> p1 x = p2 x) -> List.any p1 xs = List.any p2 xs
  | Nil, ep => rfl
  | Cons x xs, ep => rewrite ep x (Inl rfl), List.anyCongMem p1 p2 xs (y m => ep y (Inr m))

theorem List.occurrencesCongMem (p1: a -> Bool) (p2: a -> Bool): (xs: List a) -> ((x: a) -> (m: List.Mem x xs) -> p1 x = p2 x) ->
    List.occurrences p1 xs = List.occurrences p2 xs
  | Nil, ep => rfl
  | Cons x xs, ep => rewrite ep x (Inl rfl), List.occurrencesCongMem p1 p2 xs (y m => ep y (Inr m))

theorem List.foldLeftCongMem (f1: b -> a -> b) (f2: b -> a -> b): (z: b) -> (xs: List a) -> ((acc: b) -> (x: a) -> (m: List.Mem x xs) -> f1 acc x = f2 acc x) ->
    List.foldLeft f1 z xs = List.foldLeft f2 z xs
  | z, Nil, ef => rfl
  | z, Cons x xs, ef =>
    Eq.trans (Eq.cong (t => List.foldLeft f1 t xs) (ef z x (Inl rfl))) (List.foldLeftCongMem f1 f2 (f2 z x) xs (acc y m => ef acc y (Inr m)))

-- Over a run of numbers, the facts are the run's bounds. `rewrite` tries a
-- function's `…CongRange` lemma first, then `…CongMem`, then `…Cong`, and
-- rewriting inside the function has the facts as hypotheses.
theorem List.mapCongRange (f1: Nat -> b) (f2: Nat -> b) (c: Nat) (s: Nat)
    (ef: (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> f1 x = f2 x):
    List.map f1 (List.rangeFrom c s) = List.map f2 (List.rangeFrom c s) :=
  List.mapCongMem f1 f2 (List.rangeFrom c s) (x m => ef x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.filterCongRange (p1: Nat -> Bool) (p2: Nat -> Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> p1 x = p2 x):
    List.filter p1 (List.rangeFrom c s) = List.filter p2 (List.rangeFrom c s) :=
  List.filterCongMem p1 p2 (List.rangeFrom c s) (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.anyCongRange (p1: Nat -> Bool) (p2: Nat -> Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> p1 x = p2 x):
    List.any p1 (List.rangeFrom c s) = List.any p2 (List.rangeFrom c s) :=
  List.anyCongMem p1 p2 (List.rangeFrom c s) (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.occurrencesCongRange (p1: Nat -> Bool) (p2: Nat -> Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> p1 x = p2 x):
    List.occurrences p1 (List.rangeFrom c s) = List.occurrences p2 (List.rangeFrom c s) :=
  List.occurrencesCongMem p1 p2 (List.rangeFrom c s) (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.foldLeftCongRange (f1: b -> Nat -> b) (f2: b -> Nat -> b) (z: b) (c: Nat) (s: Nat)
    (ef: (acc: b) -> (x: Nat) -> (low: s <= x) -> (high: x < s + c) -> f1 acc x = f2 acc x):
    List.foldLeft f1 z (List.rangeFrom c s) = List.foldLeft f2 z (List.rangeFrom c s) :=
  List.foldLeftCongMem f1 f2 z (List.rangeFrom c s)
    (acc x m => ef acc x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

test "List.pairsMap" := (List.map Succ [1, 2, 3]).pairs == List.map (p => MkPair (Succ p.fst) (Succ p.snd)) [1, 2, 3].pairs

-- the largest by folding Nat.max --------------------------------------------

-- The fold starts at `start` and never goes down.
theorem List.foldMaxGe: (start: Nat) -> (xs: List Nat) -> start <= List.foldLeft Nat.max start xs
  | start, Nil => Nat.leRefl start
  | start, Cons x xs => Nat.leTrans start (Nat.max start x) (List.foldLeft Nat.max (Nat.max start x) xs) (Nat.leMaxLeft start x) (List.foldMaxGe (Nat.max start x) xs)

-- Every element is at most the largest.
theorem List.leFoldMax (x: Nat): (start: Nat) -> (xs: List Nat) -> List.Mem x xs -> x <= List.foldLeft Nat.max start xs
  | start, Nil, m => Void.exfalso m
  | start, Cons y ys, Inl e => rewrite <- e in Nat.leTrans y (Nat.max start y) (List.foldLeft Nat.max (Nat.max start y) ys) (Nat.leMaxRight start y) (List.foldMaxGe (Nat.max start y) ys)
  | start, Cons y ys, Inr m => List.leFoldMax x (Nat.max start y) ys m

-- The largest is the start or one of the elements.
theorem List.foldMaxMem: (start: Nat) -> (xs: List Nat) -> Or (List.foldLeft Nat.max start xs = start) (List.Mem (List.foldLeft Nat.max start xs) xs)
  | start, Nil => Inl rfl
  | start, Cons y ys =>
    match List.foldMaxMem (Nat.max start y) ys with
      | Inr m => Inr (Inr m)
      | Inl e =>
        match h: Nat.leq start y with
          | True => Inr (Inl (Eq.sym e))
          | False => Inl e

-- lengths, and sums over ranges ---------------------------------------------

-- Zipping two lists of at least n elements gives at least n.
theorem List.lengthZipWithAtLeast (f: a -> b -> c): (n: Nat) -> (u: List a) -> (v: List b) -> n <= List.length u -> n <= List.length v ->
    n <= List.length (List.zipWith f u v)
  | Zero, u, v, hu, hv => rfl
  | Succ n, Nil, v, hu, hv => hu
  | Succ n, Cons x xs, Nil, hu, hv => hv
  | Succ n, Cons x xs, Cons y ys, hu, hv => List.lengthZipWithAtLeast f n xs ys hu hv

-- Running results: one more than the elements, the start first.
theorem List.lengthScanLeft (f: b -> a -> b): (start: b) -> (xs: List a) -> List.length (List.scanLeft f start xs) = Succ (List.length xs)
  | start, Nil => rfl
  | start, Cons x xs => Eq.cong Succ (List.lengthScanLeft f (f start x) xs)

-- A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem List.sumByRangeSplit (f: Nat -> Nat) (t: Nat) (b: Nat) (tb: t <= b):
    List.sumBy f (List.rangeFrom b 0) = List.sumBy f (List.rangeFrom t 0) + List.sumBy f (List.rangeFrom (b - t) t) :=
  calc List.sumBy f (List.rangeFrom b 0)
    _ = List.sumBy f (List.rangeFrom (t + (b - t)) 0) := Eq.cong (n => List.sumBy f (List.rangeFrom n 0)) (Eq.sym (Nat.addSubCancel t b tb))
    _ = List.sumBy f (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) := Eq.cong (List.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy f (List.rangeFrom t 0) + List.sumBy f (List.rangeFrom (b - t) t) := List.sumByAppend f (List.rangeFrom t 0) (List.rangeFrom (b - t) t)

-- sums of zero -----------------------------------------------------------------

-- A sum of numbers is 0 only if each is.
theorem List.sumByZeroElim (f: a -> Nat): (xs: List a) -> List.sumBy f xs = 0 -> (x: a) -> List.Mem x xs -> f x = 0
  | Nil, h, x, m => Void.exfalso m
  | Cons y ys, h, x, Inl e => rewrite <- e in (Nat.addEqZero (f y) (List.sumBy f ys) (Eq.trans (Eq.sym (List.sumByCons f y ys)) h)).left
  | Cons y ys, h, x, Inr m => List.sumByZeroElim f ys (Nat.addEqZero (f y) (List.sumBy f ys) (Eq.trans (Eq.sym (List.sumByCons f y ys)) h)).right x m

theorem List.sumByZeroIntro (f: a -> Nat): (xs: List a) -> ((x: a) -> List.Mem x xs -> f x = 0) -> List.sumBy f xs = 0
  | Nil, h => rfl
  | Cons y ys, h => rewrite List.sumByCons f y ys, h y (Inl rfl), List.sumByZeroIntro f ys (x m => h x (Inr m)) in rfl

-- filtering what can't pass anyway ------------------------------------------

-- Dropping elements that fail `q`, when only elements that pass `q` can pass
-- `p`, changes neither `any p` nor `count p`.
theorem List.anyFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True): (xs: List a) -> List.any p (List.filter q xs) = List.any p xs
  | Nil => rfl
  | Cons x xs =>
    match e: q x with
      | True => rewrite List.anyFilter p q h xs in rfl
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.anyFilter p q h xs

theorem List.countFromFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True): (n: Nat) -> (xs: List a) ->
    List.foldLeft (k x => Nat.succIf k (p x)) n (List.filter q xs) = List.foldLeft (k x => Nat.succIf k (p x)) n xs
  | n, Nil => rfl
  | n, Cons x xs =>
    match e: q x with
      | True => List.countFromFilter p q h (Nat.succIf n (p x)) xs
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.countFromFilter p q h n xs

theorem List.countFilter (p: a -> Bool) (q: a -> Bool) (h: (x: a) -> p x = True -> q x = True) (xs: List a): List.count p (List.filter q xs) = List.count p xs :=
  List.countFromFilter p q h 0 xs

-- membership through zip, take, drop and filter ------------------------------

-- Each pair of `List.zip xs ys` is an element of `xs` with one of `ys`.
theorem List.memZip (p: (a, b)): (xs: List a) -> (ys: List b) -> List.Mem p (List.zip xs ys) -> And (List.Mem p.fst xs) (List.Mem p.snd ys)
  | Nil, ys, m => Void.exfalso m
  | Cons x xs, Nil, m => Void.exfalso m
  | Cons x xs, Cons y ys, Inl e => rewrite <- e in Both (Inl rfl) (Inl rfl)
  | Cons x xs, Cons y ys, Inr m =>
    match List.memZip p xs ys m with
      | Both inXs inYs => Both (Inr inXs) (Inr inYs)

theorem List.memTake (v: a): (n: Nat) -> (xs: List a) -> List.Mem v (List.take n xs) -> List.Mem v xs
  | Zero, xs, m => Void.exfalso m
  | Succ n, Nil, m => m
  | Succ n, Cons x xs, Inl e => Inl e
  | Succ n, Cons x xs, Inr m => Inr (List.memTake v n xs m)

theorem List.memDrop (v: a): (n: Nat) -> (xs: List a) -> List.Mem v (List.drop n xs) -> List.Mem v xs
  | Zero, xs, m => m
  | Succ n, Nil, m => m
  | Succ n, Cons x xs, m => Inr (List.memDrop v n xs m)

-- What passes the test is kept.
theorem List.memFilterIntro (p: a -> Bool) (v: a): (xs: List a) -> List.Mem v xs -> p v = True -> List.Mem v (List.filter p xs)
  | Nil, m, h => m
  | Cons x xs, Inl e, h => rewrite <- e at h in (rewrite h in Inl e)
  | Cons x xs, Inr m, h =>
    match e: p x with
      | True => Inr (List.memFilterIntro p v xs m h)
      | False => List.memFilterIntro p v xs m h

-- Filtering a mapped list is mapping the filtered list.
theorem List.filterOfMap (q: b -> Bool) (g: a -> b): (xs: List a) -> List.filter q (List.map g xs) = List.map g (List.filter (x => q (g x)) xs)
  | Nil => rfl
  | Cons x xs =>
    match e: q (g x) with
      | True => rewrite List.filterOfMap q g xs in rfl
      | False => List.filterOfMap q g xs

-- Each pair of `List.pairs xs` is two elements of `xs`.
theorem List.memPairs (p: (a, a)): (xs: List a) -> List.Mem p (List.pairs xs) -> And (List.Mem p.fst xs) (List.Mem p.snd xs)
  | Nil, m => Void.exfalso m
  | Cons x xs, m =>
    match List.memAppend p (List.map (y => (x, y)) xs) (List.pairs xs) m with
      | Inl first =>
        List.anyElim (y => (x, y) = p) (And (List.Mem p.fst (Cons x xs)) (List.Mem p.snd (Cons x xs))) xs (List.memMapAny (y => (x, y)) p xs first)
          (y inXs e => rewrite <- e in Both (Inl rfl) (Inr inXs))
      | Inr later =>
        match List.memPairs p xs later with
          | Both one other => Both (Inr one) (Inr other)
