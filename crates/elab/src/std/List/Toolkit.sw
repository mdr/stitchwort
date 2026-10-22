-- The list toolkit: `map`, `filter`, folds, sums, `zip`, `take`/`drop`, `get`,
-- `splitBy`, padding, transpose and their lemmas. This file was the prelude's
-- "List toolkit" block and the list lemmas beside it.

theorem List.lengthAppend: (xs: List a) -> (ys: List a) -> List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil,       ys => rfl
  | Cons x xs, ys => Eq.cong Succ (List.lengthAppend xs ys)

-- List toolkit. The callbacks are pure: the library has no convention yet for
-- callbacks with effects or `Partial`. Every function is structurally recursive.

def List.map (f: a -> b): List a -> List b
  | Nil       => Nil
  | Cons x xs => Cons (f x) (List.map f xs)

-- One step of `List.filter`: `x` in front of the filtered rest, or not. A
-- function of its own so the recursive call is written once: with an `if`
-- around it in both branches, a condition the checker can't decide (one on
-- a variable) keeps both branches, and the value doubles with every element.
def List.filterStep (x: a) (rest: List a): Bool -> List a
  | True  => Cons x rest
  | False => rest

def List.filter (p: a -> Bool): List a -> List a
  | Nil       => Nil
  | Cons x xs => List.filterStep x (List.filter p xs) (p x)

-- Left fold; tail-recursive. `List.foldLeft f z [x, y]` is `f (f z x) y`.
def List.foldLeft (f: b -> a -> b) (z: b): List a -> b
  | Nil       => z
  | Cons x xs => List.foldLeft f (f z x) xs

-- Running accumulations, the initial value first (Haskell's `scanLeft`):
-- `List.scanLeft f z [x, y]` is `[z, f z x, f (f z x) y]`. Always one longer than
-- the input.
def List.scanLeft (f: b -> a -> b) (z: b): List a -> List b
  | Nil       => Cons z Nil
  | Cons x xs => Cons z (List.scanLeft f (f z x) xs)

theorem List.scanLeftNil: List.scanLeft (acc x => acc + x) 5 Nil = [5] := rfl

theorem List.scanLeftSums: List.scanLeft (acc x => acc + x) 0 [1, 2, 3] = [0, 1, 3, 6] := rfl

-- Right fold. `List.foldRight f z [x, y]` is `f x (f y z)`.
def List.foldRight (f: a -> b -> b) (z: b): List a -> b
  | Nil       => z
  | Cons x xs => f x (List.foldRight f z xs)

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
  | Nil       => None
  | Cons x xs => Some (List.foldLeft Ord.max x xs)

def List.minimum [auto ord: Ord a]: List a -> Option a
  | Nil       => None
  | Cons x xs => Some (List.foldLeft Ord.min x xs)

-- Pairs up to the shorter list's length.
def List.zip: List a -> List b -> List (Pair a b)
  | Nil,       ys        => Nil
  | Cons x xs, Nil       => Nil
  | Cons x xs, Cons y ys => Cons (MkPair x y) (List.zip xs ys)

def List.zipWith (f: a -> b -> c): List a -> List b -> List c
  | Nil,       ys        => Nil
  | Cons x xs, Nil       => Nil
  | Cons x xs, Cons y ys => Cons (f x y) (List.zipWith f xs ys)

-- Combines three lists up to the shortest list's length.
def List.zipWith3 (f: a -> b -> c -> d): List a -> List b -> List c -> List d
  | Nil,       ys,        zs        => Nil
  | Cons x xs, Nil,       zs        => Nil
  | Cons x xs, Cons y ys, Nil       => Nil
  | Cons x xs, Cons y ys, Cons z zs => Cons (f x y z) (List.zipWith3 f xs ys zs)

-- The first n elements (all of them if there are fewer).
def List.take: Nat -> List a -> List a
  | Zero,   xs        => Nil
  | Succ n, Nil       => Nil
  | Succ n, Cons x xs => Cons x (List.take n xs)

-- All but the first n elements.
def List.drop: Nat -> List a -> List a
  | Zero,   xs        => xs
  | Succ n, Nil       => Nil
  | Succ n, Cons x xs => List.drop n xs

-- The element at index i, counting from 0.
def List.get: Nat -> List a -> Option a
  | i,      Nil       => None
  | Zero,   Cons x xs => Some x
  | Succ i, Cons x xs => List.get i xs

def List.any (p: a -> Bool): List a -> Bool
  | Nil       => False
  | Cons x xs => if p x then True else List.any p xs

def List.all (p: a -> Bool): List a -> Bool
  | Nil       => True
  | Cons x xs => if p x then List.all p xs else False

-- `n`, plus one if `b`: `List.count`'s step. A function of its own so `n` is
-- written once: `if b then Succ n else n` writes it twice, so when the
-- checker can't decide the conditions, a count doubles in size with every
-- element.
def Nat.succIf (n: Nat): Bool -> Nat
  | True  => Succ n
  | False => n

-- How many elements satisfy `p`.
def List.count (p: a -> Bool) (xs: List a): Nat := List.foldLeft (n x => Nat.succIf n (p x)) 0 xs

-- The first element satisfying `p`.
def List.find (p: a -> Bool): List a -> Option a
  | Nil       => None
  | Cons x xs => if p x then Some x else List.find p xs

def List.consSome: Option b -> List b -> List b
  | None, rest => rest
  | Some y,  rest => Cons y rest

-- Keeps the `Some` results, in order.
def List.filterMap (f: a -> Option b): List a -> List b
  | Nil       => Nil
  | Cons x xs => List.consSome (f x) (List.filterMap f xs)

-- Joins a list of lists.
def List.concat: List (List a) -> List a
  | Nil         => Nil
  | Cons xs xss => List.append xs (List.concat xss)

-- `List.replicate n x` is n copies of x.
def List.replicate: Nat -> a -> List a
  | Zero,   x => Nil
  | Succ n, x => Cons x (List.replicate n x)

def List.rangeFrom: Nat -> Nat -> List Nat
  | Zero,   i => Nil
  | Succ n, i => Cons i (List.rangeFrom n (Succ i))

-- A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend: (a: Nat) -> (b: Nat) -> (s: Nat) -> List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a))
  | Zero,   b, s => Eq.cong (t => List.rangeFrom b t) (Eq.sym (Nat.addZero s))
  | Succ a, b, s =>
    Eq.cong (Cons s) (Eq.trans (List.rangeFromAppend a b (Succ s)) (Eq.cong (t => List.append (List.rangeFrom a (Succ s)) (List.rangeFrom b t)) (Eq.sym (Nat.addSucc s a))))

-- `List.range n` is `[0, 1, ..., n - 1]`.
def List.range (n: Nat): List Nat := List.rangeFrom n 0

def List.reverse (xs: List a): List a := List.reverseOnto xs Nil

def List.last: List a -> Option a
  | Nil                => None
  | Cons x Nil         => Some x
  | Cons x (Cons y ys) => List.last (Cons y ys)

-- The first element, or `None` for an empty list.
def List.head: List a -> Option a
  | Nil       => None
  | Cons x xs => Some x

theorem List.headExample: List.head [3, 4] = Some 3 := rfl

theorem List.headEmpty: List.head (Nil: List Nat) = None := rfl

-- All but the last element (`Nil` for an empty list).
def List.init: List a -> List a
  | Nil                => Nil
  | Cons x Nil         => Nil
  | Cons x (Cons y ys) => Cons x (List.init (Cons y ys))

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := rfl

theorem List.initEmpty: List.init (Nil: List Nat) = Nil := rfl

-- Membership, given a decision for equality (as `List.decEq` takes).
def List.elem (d: (x: a) -> (y: a) -> Decidable (x = y)) (z: a): List a -> Bool
  | Nil       => False
  | Cons x xs => if Decidable.toBool (d z x) then True else List.elem d z xs

-- The elements that satisfy `p`, and those that don't.
def List.partition (p: a -> Bool) (xs: List a): Pair (List a) (List a) := MkPair (List.filter p xs) (List.filter (x => !(p x)) xs)

-- The value for the first pair whose key is equal, given a decision for equality.
def List.lookup (d: (x: k) -> (y: k) -> Decidable (x = y)) (key: k): List (Pair k v) -> Option v
  | Nil                    => None
  | Cons (MkPair k v) rest => if Decidable.toBool (d key k) then Some v else List.lookup d key rest

-- `List.padRight n x xs` is `xs` followed by enough copies of `x` to make it
-- n long (it is `xs` itself when that is already n long or longer).
def List.padRight (n: Nat) (x: a) (xs: List a): List a := List.append xs (List.replicate (n - List.length xs) x)

theorem List.lengthReplicate (x: a): (n: Nat) -> List.length (List.replicate n x) = n
  | Zero   => rfl
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
  | Zero,   rows => Nil
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
  | Nil       => rfl
  | Cons x xs => Eq.cong Succ (List.lengthMap f xs)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := rfl

theorem List.transposeNone: List.transpose (Nil: List (List Nat)) = Nil := rfl

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := rfl

theorem List.transposeNLength: (n: Nat) -> (rows: List (List a)) -> List.length (List.transposeN n rows) = n
  | Zero,   rows => rfl
  | Succ n, rows => Eq.cong Succ (List.transposeNLength n (List.map (List.drop 1) rows))

-- Every element of the list satisfies `p`.
def List.All (p: a -> Prop): List a -> Prop
  | Nil       => Unit
  | Cons x xs => And (p x) (List.All p xs)

-- Some element of the list satisfies `p`.
def List.Any (p: a -> Prop): List a -> Prop
  | Nil       => Void
  | Cons x xs => Or (p x) (List.Any p xs)

theorem List.allAppend (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p xs -> List.All p ys -> List.All p (List.append xs ys)
  | Nil,       ys, hx, hy => hy
  | Cons x xs, ys, Both hx hxs, hy => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p (List.append xs ys) -> List.All p xs
  | Nil,       ys, h => Trivial
  | Cons x xs, ys, Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.All p (List.append xs ys) -> List.All p ys
  | Nil,       ys, h => h
  | Cons x xs, ys, Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap (p: b -> Prop) (f: a -> b): (xs: List a) -> List.All (x => p (f x)) xs -> List.All p (List.map f xs)
  | Nil,       h => Trivial
  | Cons x xs, Both h hxs => Both h (List.allMap p f xs hxs)

theorem List.allImplies (p: a -> Prop) (q: a -> Prop) (h: (x: a) -> p x -> q x): (xs: List a) -> List.All p xs -> List.All q xs
  | Nil,       hp => Trivial
  | Cons x xs, Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft (p: a -> Prop): (xs: List a) -> (ys: List a) -> List.Any p xs -> List.Any p (List.append xs ys)
  | Nil,       ys, h => Void.exfalso h
  | Cons x xs, ys, Inl h => Inl h
  | Cons x xs, ys, Inr h => Inr (List.anyAppendLeft p xs ys h)

-- `List.any` of two lists joined: either list has one.
theorem List.anyAppend (p: a -> Bool): (xs: List a) -> (ys: List a) -> List.any p (List.append xs ys) = (List.any p xs || List.any p ys)
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    match e: p x with
      | True  => rfl
      | False => List.anyAppend p xs ys

theorem List.anyAppendExample: List.any (x => x == 3) (List.append [1, 2] [3]) = (False || True) := rfl

-- Every row has length n (the list is rectangular).
def List.AllLength (n: Nat): List (List a) -> Prop
  | Nil       => Unit
  | Cons r rs => And (List.length r = n) (List.AllLength n rs)

theorem List.lengthZero: (xs: List a) -> List.length xs = 0 -> xs = Nil
  | Nil,       h => rfl
  | Cons y ys, h => Void.exfalso (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil: (n: Nat) -> List.transposeN n (Nil: List (List a)) = List.replicate n Nil
  | Zero   => rfl
  | Succ n => Eq.cong (Cons Nil) (List.transposeNNil n)

theorem List.allLengthZero: (rows: List (List a)) -> (n: Nat) -> List.length rows = n -> List.AllLength 0 rows ->
    rows = List.replicate n Nil
  | Nil,        n,      hl, hr          => J (y q => (Nil: List (List a)) = List.replicate y (Nil: List a)) rfl hl
  | Cons r rs,  Zero,   hl, hr          => Void.exfalso (Nat.succNotZero (List.length rs) hl)
  | Cons r rs,  Succ m, hl, Both hr hrs =>
    Eq.trans (Eq.cong (t => Cons t rs) (List.lengthZero r hr))
      (Eq.cong (Cons Nil) (List.allLengthZero rs m (Nat.succInjective (List.length rs) m hl) hrs))

theorem List.tailsAllLength (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    List.AllLength k (List.map (List.drop 1) rows)
  | Nil,              hr          => Trivial
  | Cons Nil rs,      Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Both (Nat.succInjective (List.length ys) k hr) (List.tailsAllLength k rs hrs)

theorem List.headsLength (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    List.length (List.filterMap (List.get 0) rows) = List.length rows
  | Nil,              hr          => rfl
  | Cons Nil rs,      Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Eq.cong Succ (List.headsLength k rs hrs)

theorem List.rowsAreHeadsAndTails (k: Nat): (rows: List (List a)) -> List.AllLength (Succ k) rows ->
    rows = List.zipWith Cons (List.filterMap (List.get 0) rows) (List.map (List.drop 1) rows)
  | Nil,              hr          => rfl
  | Cons Nil rs,      Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, Both hr hrs => Eq.cong (Cons (Cons y ys)) (List.rowsAreHeadsAndTails k rs hrs)

theorem List.columnsAllLength: (w: Nat) -> (rows: List (List a)) -> (h: Nat) -> List.length rows = h -> List.AllLength w rows ->
    List.AllLength h (List.transposeN w rows)
  | Zero,   rows, h, hl, hr => Trivial
  | Succ k, rows, h, hl, hr =>
    Both (Eq.trans (List.headsLength k rows hr) hl)
      (List.columnsAllLength k (List.map (List.drop 1) rows) h (Eq.trans (List.lengthMap (List.drop 1) rows) hl) (List.tailsAllLength k rows hr))

theorem List.transposeNCons: (h: Nat) -> (heads: List a) -> (cols: List (List a)) -> List.length heads = h -> List.AllLength h cols ->
    List.transposeN h (Cons heads cols) = List.zipWith Cons heads (List.transposeN h cols)
  | Zero,   Nil,        cols, hl, hc => rfl
  | Zero,   Cons x xs,  cols, hl, hc => Void.exfalso (Nat.succNotZero (List.length xs) hl)
  | Succ m, Nil,        cols, hl, hc => Void.exfalso (Nat.zeroNotSucc m hl)
  | Succ m, Cons x xs,  cols, hl, hc =>
    Eq.cong (Cons (Cons x (List.filterMap (List.get 0) cols)))
      (List.transposeNCons m xs (List.map (List.drop 1) cols) (Nat.succInjective (List.length xs) m hl) (List.tailsAllLength m cols hc))

theorem List.transposeNTwice: (w: Nat) -> (h: Nat) -> (rows: List (List a)) -> List.length rows = h -> List.AllLength w rows ->
    List.transposeN h (List.transposeN w rows) = rows
  | Zero,   h, rows, hl, hr => Eq.trans (List.transposeNNil h) (Eq.sym (List.allLengthZero rows h hl hr))
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
  | Nil,        hr          => rfl
  | Cons r rs,  Both hr hrs =>
    J (y q => List.transposeN (List.length (List.headOr Nil (List.transposeN y (Cons r rs)))) (List.transposeN y (Cons r rs)) = Cons r rs)
      (List.transposeNTwice (Succ k) (List.length (List.headOr Nil (List.transposeN (Succ k) (Cons r rs)))) (Cons r rs)
        (Eq.sym (List.headsLength k (Cons r rs) (Both hr hrs))) (Both hr hrs))
      (Eq.sym hr)

-- The groups of consecutive elements that don't satisfy `p`, in order: `p`
-- marks the separators, which are dropped, and no group is empty. So
-- `List.splitBy (x => x == 0) [1, 2, 0, 0, 3]` is `[[1, 2], [3]]`.
def List.splitBy (p: a -> Bool) (xs: List a): List (List a) := List.finishGroups (List.splitGroups p xs)

-- Reads the list from the right: the group still open at the front, and the
-- groups finished after it.
def List.splitGroups (p: a -> Bool): List a -> Pair (List a) (List (List a))
  | Nil       => MkPair Nil Nil
  | Cons x xs => List.splitStep x (p x) (List.splitGroups p xs)

-- Adds the element `x` in front: a separator (`True`) closes the open group,
-- anything else joins it.
def List.splitStep (x: a): Bool -> Pair (List a) (List (List a)) -> Pair (List a) (List (List a))
  | True,  MkPair cur done => MkPair Nil (List.closeGroup cur done)
  | False, MkPair cur done => MkPair (Cons x cur) done

def List.finishGroups: Pair (List a) (List (List a)) -> List (List a)
  | MkPair cur done => List.closeGroup cur done

-- Adds a group to the finished ones, unless it is empty.
def List.closeGroup: List a -> List (List a) -> List (List a)
  | Nil,       done => done
  | Cons y ys, done => Cons (Cons y ys) done

def List.splitTotal (st: Pair (List a) (List (List a))): Nat := List.length (Pair.fst st) + List.sumBy List.length (Pair.snd st)

theorem List.closeGroupSum: (cur: List a) -> (done: List (List a)) ->
    List.sumBy List.length (List.closeGroup cur done) = List.length cur + List.sumBy List.length done
  | Nil,       done => rfl
  | Cons y ys, done => List.sumByCons List.length (Cons y ys) done

theorem List.splitStepTotal (x: a): (b: Bool) -> (st: Pair (List a) (List (List a))) ->
    List.splitTotal (List.splitStep x b st) + Bool.toNat b = Succ (List.splitTotal st)
  | True,  MkPair cur done =>
    Eq.trans (Nat.addOne (List.sumBy List.length (List.closeGroup cur done))) (Eq.cong Succ (List.closeGroupSum cur done))
  | False, MkPair cur done => Nat.addZero (Succ (List.length cur + List.sumBy List.length done))

theorem List.splitGroupsTotal (p: a -> Bool): (xs: List a) ->
    List.splitTotal (List.splitGroups p xs) + List.occurrences p xs = List.length xs
  | Nil       => rfl
  | Cons x xs =>
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
  | Nil       => Unit
  | Cons g gs => And (And (0 < List.length g) (List.NonSep p g)) (List.Groups p gs)

def List.SplitOk (p: a -> Bool): Pair (List a) (List (List a)) -> Prop
  | MkPair cur done => And (List.NonSep p cur) (List.Groups p done)

theorem List.closeGroupGroups (p: a -> Bool): (cur: List a) -> (done: List (List a)) -> List.NonSep p cur -> List.Groups p done ->
    List.Groups p (List.closeGroup cur done)
  | Nil,       done, hc, hd => hd
  | Cons y ys, done, hc, hd => Both (Both (Nat.zeroLe (List.length ys)) hc) hd

theorem List.nonSepCons (p: a -> Bool) (x: a) (cur: List a) (h: p x = False) (hc: List.NonSep p cur): List.NonSep p (Cons x cur) :=
  rewrite h in hc

theorem List.splitStepOk (p: a -> Bool) (x: a): (b: Bool) -> p x = b -> (st: Pair (List a) (List (List a))) -> List.SplitOk p st ->
    List.SplitOk p (List.splitStep x b st)
  | True,  e, MkPair cur done, Both hc hd => Both rfl (List.closeGroupGroups p cur done hc hd)
  | False, e, MkPair cur done, Both hc hd => Both (List.nonSepCons p x cur e hc) hd

theorem List.splitGroupsOk (p: a -> Bool): (xs: List a) -> List.SplitOk p (List.splitGroups p xs)
  | Nil       => Both rfl Trivial
  | Cons x xs => List.splitStepOk p x (p x) rfl (List.splitGroups p xs) (List.splitGroupsOk p xs)

theorem List.finishGroupsOk (p: a -> Bool): (st: Pair (List a) (List (List a))) -> List.SplitOk p st -> List.Groups p (List.finishGroups st)
  | MkPair cur done, Both hc hd => List.closeGroupGroups p cur done hc hd

-- No group is empty, and none has a separator in it.
theorem List.splitByGroups (p: a -> Bool) (xs: List a): List.Groups p (List.splitBy p xs) :=
  List.finishGroupsOk p (List.splitGroups p xs) (List.splitGroupsOk p xs)

theorem List.closeGroupConcat: (cur: List a) -> (done: List (List a)) ->
    List.concat (List.closeGroup cur done) = List.append cur (List.concat done)
  | Nil,       done => rfl
  | Cons y ys, done => rfl

def List.SplitKeeps (p: a -> Bool) (xs: List a) (st: Pair (List a) (List (List a))): Prop :=
  List.append (Pair.fst st) (List.concat (Pair.snd st)) = List.filter (x => !(p x)) xs

theorem List.splitStepKeeps (p: a -> Bool) (x: a) (xs: List a): (b: Bool) -> p x = b -> (st: Pair (List a) (List (List a))) ->
    List.SplitKeeps p xs st -> List.SplitKeeps p (Cons x xs) (List.splitStep x b st)
  | True,  e, MkPair cur done, h =>
    Eq.trans (List.closeGroupConcat cur done)
      (Eq.trans h (Eq.sym (List.filterSkip (z => !(p z)) x xs (Eq.cong Bool.not e))))
  | False, e, MkPair cur done, h =>
    Eq.trans (Eq.cong (Cons x) h) (Eq.sym (List.filterKeep (z => !(p z)) x xs (Eq.cong Bool.not e)))

theorem List.splitGroupsKeeps (p: a -> Bool): (xs: List a) -> List.SplitKeeps p xs (List.splitGroups p xs)
  | Nil       => rfl
  | Cons x xs => List.splitStepKeeps p x xs (p x) rfl (List.splitGroups p xs) (List.splitGroupsKeeps p xs)

theorem List.finishGroupsConcat: (st: Pair (List a) (List (List a))) ->
    List.concat (List.finishGroups st) = List.append (Pair.fst st) (List.concat (Pair.snd st))
  | MkPair cur done => List.closeGroupConcat cur done

-- Joining the groups gives back the elements that aren't separators, in order.
theorem List.splitByConcat (p: a -> Bool) (xs: List a):
    List.concat (List.splitBy p xs) = List.filter (x => !(p x)) xs :=
  Eq.trans (List.finishGroupsConcat (List.splitGroups p xs)) (List.splitGroupsKeeps p xs)

-- Sums from a starting total, and one element at a time, for any `Add`:
-- the laws `zeroAdd`, `assoc` and `comm` (docs/proposals/interfaces.md §7.7).
theorem Add.addZero [auto add: Add a] (x: a): x + Add.zero = x :=
  Eq.trans (add.comm x Add.zero) (add.zeroAdd x)

theorem List.sumByFrom [auto add: Add b] (f: a -> b): (z: b) -> (xs: List a) -> List.foldLeft (acc x => acc + f x) z xs = z + List.sumBy f xs
  | z, Nil       => Eq.sym (Add.addZero z)
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
  | z, Nil,       ys => rfl
  | z, Cons x xs, ys => List.foldLeftAppend f (f z x) xs ys

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.
theorem List.appendNil: (xs: List a) -> List.append xs Nil = xs
  | Nil       => rfl
  | Cons x xs => Eq.cong (Cons x) (List.appendNil xs)

theorem List.appendAssoc: (xs: List a) -> (ys: List a) -> (zs: List a) -> List.append (List.append xs ys) zs = List.append xs (List.append ys zs)
  | Nil,       ys, zs => rfl
  | Cons x xs, ys, zs => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
def List.occurrences (p: a -> Bool): List a -> Nat
  | Nil       => 0
  | Cons x xs => Bool.toNat (p x) + List.occurrences p xs

-- `s` is `xs` with some elements left out, the rest kept in order: each
-- element of `s` is matched with an element of `xs`, or `xs`'s first element
-- is skipped.
def List.Subsequence: List a -> List a -> Prop
  | Nil,       ys        => Unit
  | Cons x xs, Nil       => Void
  | Cons x xs, Cons y ys => Or (And (x = y) (List.Subsequence xs ys)) (List.Subsequence (Cons x xs) ys)

-- Lemmas for proofs about grids: runs' lengths, `map` and `filterMap` fused,
-- `init`, `last` and `reverse` of a `map`, and transposing a grid given cell
-- by cell.
theorem List.lengthRangeFrom: (n: Nat) -> (s: Nat) -> List.length (List.rangeFrom n s) = n
  | Zero,   s => rfl
  | Succ n, s => rewrite List.lengthRangeFrom n (Succ s)

theorem List.mapMap (f: b -> c) (g: a -> b): (xs: List a) -> List.map f (List.map g xs) = List.map (x => f (g x)) xs
  | Nil       => rfl
  | Cons x xs => rewrite List.mapMap f g xs

theorem List.filterMapMap (f: b -> Option c) (g: a -> b): (xs: List a) -> List.filterMap f (List.map g xs) = List.filterMap (x => f (g x)) xs
  | Nil       => rfl
  | Cons x xs => rewrite List.filterMapMap f g xs

theorem List.filterMapSome (f: a -> b): (xs: List a) -> List.filterMap (x => Some (f x)) xs = List.map f xs
  | Nil       => rfl
  | Cons x xs => rewrite List.filterMapSome f xs

theorem List.filterMapAppend (f: a -> Option b): (xs: List a) -> (ys: List a) ->
    List.filterMap f (List.append xs ys) = List.append (List.filterMap f xs) (List.filterMap f ys)
  | Nil,       ys => rfl
  | Cons x xs, ys =>
    match f x with
      | None => List.filterMapAppend f xs ys
      | Some y  => rewrite List.filterMapAppend f xs ys

theorem List.initMap (f: a -> b): (xs: List a) -> List.init (List.map f xs) = List.map f (List.init xs)
  | Nil                => rfl
  | Cons x Nil         => rfl
  | Cons x (Cons y ys) => rewrite List.initMap f (Cons y ys)

theorem List.lastMap (f: a -> b): (xs: List a) -> List.last (List.map f xs) = Option.map f (List.last xs)
  | Nil                => rfl
  | Cons x Nil         => rfl
  | Cons x (Cons y ys) => List.lastMap f (Cons y ys)
theorem List.mapRangeShift (f: Nat -> b): (n: Nat) -> (s: Nat) ->
    List.map f (List.rangeFrom n (Succ s)) = List.map (i => f (Succ i)) (List.rangeFrom n s)
  | Zero,   s => rfl
  | Succ n, s => rewrite List.mapRangeShift f n (Succ s)

-- Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid (cell: a -> b -> c) (rows: List a): (cols: List b) ->
    List.transposeN (List.length cols) (List.map (x => List.map (cell x) cols) rows) = List.map (y => List.map (x => cell x y) rows) cols
  | Nil         => rfl
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
  | Nil,       acc => rfl
  | Cons x xs, acc => List.mapReverseOnto f xs (Cons x acc)

theorem List.mapReverse (f: a -> b) (xs: List a): List.map f (List.reverse xs) = List.reverse (List.map f xs) := List.mapReverseOnto f xs Nil

theorem List.mapCongr (f: a -> b) (g: a -> b) (h: (x: a) -> f x = g x): (xs: List a) -> List.map f xs = List.map g xs
  | Nil       => rfl
  | Cons x xs => Eq.trans (Eq.cong (y => Cons y (List.map f xs)) (h x)) (Eq.cong (ys => Cons (g x) ys) (List.mapCongr f g h xs))

theorem List.filterMapCongr (f: a -> Option b) (g: a -> Option b) (h: (x: a) -> f x = g x): (xs: List a) -> List.filterMap f xs = List.filterMap g xs
  | Nil       => rfl
  | Cons x xs => rewrite h x, List.filterMapCongr f g h xs

theorem Option.flatMapMap (g: b -> Option c) (f: a -> b): (m: Option a) -> Option.flatMap g (Option.map f m) = Option.flatMap (x => g (f x)) m
  | None => rfl
  | Some x  => rfl

theorem List.lengthZipWith3 (f: a -> b -> c -> e): (xs: List a) -> (ys: List b) -> (zs: List c) ->
    List.length ys = List.length xs -> List.length zs = List.length xs -> List.length (List.zipWith3 f xs ys zs) = List.length xs
  | Nil,       ys,        zs,        h1, h2 => rfl
  | Cons x xs, Nil,       zs,        h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil,       h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

-- A sum over a list is the sum over its indices.

-- `x` is an element of the list.
def List.Mem (x: a) (xs: List a): Prop := List.Any (y => y = x) xs

-- No element of the first list is in the second.
def List.Disjoint (xs: List a) (ys: List a): Prop := List.All (x => Not (List.Mem x ys)) xs

-- No element occurs twice.
def List.Distinct: List a -> Prop
  | Nil       => Unit
  | Cons x xs => And (Not (List.Mem x xs)) (List.Distinct xs)

theorem List.distinctNil: List.Distinct (Nil: List a) := Trivial

theorem List.distinctCons (x: a) (xs: List a) (h: Not (List.Mem x xs)) (d: List.Distinct xs): List.Distinct (Cons x xs) := Both h d

-- An element of two lists joined is in one of them.
theorem List.memAppend (x: a): (xs: List a) -> (ys: List a) -> List.Mem x (List.append xs ys) -> Or (List.Mem x xs) (List.Mem x ys)
  | Nil,       ys, h => Inr h
  | Cons z zs, ys, Inl h => Inl (Inl h)
  | Cons z zs, ys, Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- `f x` is in `List.map f xs` only if `x` is in `xs`, for an injective `f`.
theorem List.memMap (f: a -> b) (inj: (x: a) -> (y: a) -> f x = f y -> x = y) (x: a): (xs: List a) -> List.Mem (f x) (List.map f xs) -> List.Mem x xs
  | Nil,       h => h
  | Cons z zs, Inl h => Inl (inj z x h)
  | Cons z zs, Inr h => Inr (List.memMap f inj x zs h)

-- Mapping an injective function keeps a list distinct.
theorem List.distinctMap (f: a -> b) (inj: (x: a) -> (y: a) -> f x = f y -> x = y): (xs: List a) -> List.Distinct xs -> List.Distinct (List.map f xs)
  | Nil,       d => Trivial
  | Cons x xs, Both h d => Both (m => h (List.memMap f inj x xs m)) (List.distinctMap f inj xs d)

-- Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend: (xs: List a) -> (ys: List a) -> List.Distinct xs -> List.Distinct ys -> List.Disjoint xs ys -> List.Distinct (List.append xs ys)
  | Nil,       ys, dx, dy, dj => dy
  | Cons x xs, ys, Both hx dx, dy, Both hj dj =>
    Both
      (m => match List.memAppend x xs ys m with
              | Inl inXs => hx inXs
              | Inr inYs => hj inYs)
      (List.distinctAppend xs ys dx dy dj)

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both (m => match m with
               | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
               | Inr v => v)
       (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map Succ [1, 2]) :=
  List.distinctMap Succ (x y p => Nat.succInjective x y p) [1, 2] List.distinctExample

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend [1] [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both (m => match m with
                  | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
                  | Inr v => v) Trivial)

-- Mapping with a state threaded left to right (Haskell's `mapAccumL`).
-- `xs` is the main value: `xs.mapAccumLeft 0 (s x => MkPair (s + x) (s * x))`.
-- The function takes the state and an element and gives the next state and
-- the mapped element; the result is the final state and the mapped list.
def List.mapAccumLeftGo (f: s -> a -> Pair s b) (z: s): List a -> Pair s (List b)
  | Nil       => MkPair z Nil
  | Cons x xs => List.mapAccumLeftStep f xs (f z x)

def List.mapAccumLeftStep (f: s -> a -> Pair s b) (xs: List a): Pair s b -> Pair s (List b)
  | MkPair z y => List.mapAccumLeftCons y (List.mapAccumLeftGo f z xs)

def List.mapAccumLeftCons (y: b): Pair s (List b) -> Pair s (List b)
  | MkPair z ys => MkPair z (Cons y ys)

def List.mapAccumLeft (xs: List a) (z: s) (f: s -> a -> Pair s b): Pair s (List b) := List.mapAccumLeftGo f z xs

-- Splits a list of pairs into the list of firsts and the list of seconds.
def List.unzipCons (x: a) (y: b): Pair (List a) (List b) -> Pair (List a) (List b)
  | MkPair xs ys => MkPair (Cons x xs) (Cons y ys)

def List.unzip: List (Pair a b) -> Pair (List a) (List b)
  | Nil                  => MkPair Nil Nil
  | Cons (MkPair x y) ps => List.unzipCons x y (List.unzip ps)

-- Dropping elements never makes a list longer.
theorem List.lengthDropLe: (n: Nat) -> (xs: List a) -> List.length (List.drop n xs) <= List.length xs
  | Zero,   xs        => Nat.leRefl (List.length xs)
  | Succ n, Nil       => rfl
  | Succ n, Cons x xs => Nat.leTrans (List.length (List.drop n xs)) (List.length xs) (Succ (List.length xs)) (List.lengthDropLe n xs) (Nat.leSucc (List.length xs))

-- Dropping at least one element of a non-empty list leaves a shorter list.
theorem List.dropConsLess: (n: Nat) -> (x: a) -> (xs: List a) -> n != 0 -> List.length (List.drop n (Cons x xs)) < List.length (Cons x xs)
  | Zero,   x, xs, h => Void.exfalso (h rfl)
  | Succ n, x, xs, h => Nat.leLessSucc (List.length (List.drop n xs)) (List.length xs) (List.lengthDropLe n xs)

-- Chunks of `n` elements, in order; the last chunk is shorter when `n` doesn't
-- divide the length. `n = 0` is no sensible chunk size, so it gives the whole
-- list as one chunk (`[xs]`, or `[]` for an empty `xs`).
def List.chunksOfPositive (n: Nat) (xs: List a) [auto pos: n != 0]: List (List a)
  decreasing List.length xs
:=
  match xs with
    | Nil       => Nil
    | Cons y ys => Cons (List.take n (Cons y ys)) (List.chunksOfPositive n (List.drop n (Cons y ys)) [decreasing := List.dropConsLess n y ys pos])

-- `xs` is the main value: `xs.chunksOf 2`. `[1, 2, 3].chunksOf 2` is
-- `[[1, 2], [3]]`.
def List.chunksOf (xs: List a) (n: Nat): List (List a) :=
  match n with
    | Zero   => match xs with
                  | Nil       => Nil
                  | Cons y ys => Cons (Cons y ys) Nil
    | Succ k => List.chunksOfPositive (Succ k) xs

-- The elements without repeats, keeping the first occurrence of each and the
-- order. `seen` is what came before. Needs `DecEq`; quadratic.
def List.distinctFrom [auto eq: DecEq a] (seen: List a): List a -> List a
  | Nil       => Nil
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
  | _    => best

def List.maxBy [auto ord: Ord b] (xs: List a) (f: a -> b): Option a :=
  match xs with
    | Nil       => None
    | Cons x ys => Some (List.foldLeft (best y => List.maxByStep f best y) x ys)

-- The element with the smallest key; on a tie the FIRST one wins, as for
-- `List.maxBy`.
def List.minByStep [auto ord: Ord b] (f: a -> b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Greater => x
  | _       => best

def List.minBy [auto ord: Ord b] (xs: List a) (f: a -> b): Option a :=
  match xs with
    | Nil       => None
    | Cons x ys => Some (List.foldLeft (best y => List.minByStep f best y) x ys)

-- The longest prefix of elements satisfying `p`.
def List.takeWhile (xs: List a) (p: a -> Bool): List a :=
  match xs with
    | Nil       => Nil
    | Cons x ys => if p x then Cons x (List.takeWhile ys p) else Nil

-- What is left after `List.takeWhile`: from the first element not satisfying `p`.
def List.dropWhile (xs: List a) (p: a -> Bool): List a :=
  match xs with
    | Nil       => Nil
    | Cons x ys => if p x then List.dropWhile ys p else Cons x ys

def List.spanCons (x: a): Pair (List a) (List a) -> Pair (List a) (List a)
  | MkPair front back => MkPair (Cons x front) back

-- `List.takeWhile` and `List.dropWhile` together, in one pass.
def List.span (xs: List a) (p: a -> Bool): Pair (List a) (List a) :=
  match xs with
    | Nil       => MkPair Nil Nil
    | Cons x ys => if p x then List.spanCons x (List.span ys p) else MkPair Nil (Cons x ys)

-- The first `n` elements and the rest: `xs.splitAt 2` is `(xs.take 2, xs.drop 2)`.
def List.splitAt (xs: List a) (n: Nat): Pair (List a) (List a) := MkPair (List.take n xs) (List.drop n xs)

-- Without the last `n` elements (all of them if there are fewer).
def List.dropRight (xs: List a) (n: Nat): List a := List.take (List.length xs - n) xs

-- Every suffix, longest first, ending with the empty list:
-- `[1, 2].tails` is `[[1, 2], [2], []]`.
def List.tails: List a -> List (List a)
  | Nil       => Cons Nil Nil
  | Cons x xs => Cons (Cons x xs) (List.tails xs)

-- The index of the first element satisfying `p`.
def List.findIndexFrom (i: Nat) (p: a -> Bool): List a -> Option Nat
  | Nil       => None
  | Cons x xs => if p x then Some i else List.findIndexFrom (Succ i) p xs

def List.findIndex (xs: List a) (p: a -> Bool): Option Nat := List.findIndexFrom 0 p xs

-- Each element with its index from `i`.
def List.withIndexFrom (i: Nat): List a -> List (Pair Nat a)
  | Nil       => Nil
  | Cons x xs => Cons (MkPair i x) (List.withIndexFrom (Succ i) xs)

-- Pairs each element with its position, counting from 0, the position first
-- (Rust's `enumerate`): `["a", "b"].withIndex` is `[(0, "a"), (1, "b")]`.
def List.withIndex (xs: List a): List (Pair Nat a) := List.withIndexFrom 0 xs

-- The first option if it is a `Some`, else the second.
def List.orElseSome: Option b -> Option b -> Option b
  | Some y, rest => Some y
  | None,   rest => rest

-- The first `Some` that `f` gives (Lean's `findSome?`, Scala's `collectFirst`).
def List.findMap (xs: List a) (f: a -> Option b): Option b :=
  match xs with
    | Nil       => None
    | Cons x ys => List.orElseSome (f x) (List.findMap ys f)

-- Maps, then joins: `xs.flatMap f` is `List.concat (List.map f xs)`.
def List.flatMap (xs: List a) (f: a -> List b): List b := List.concat (List.map f xs)

-- Every pair, the first elements in order and the second elements within
-- each: `[1, 2].cross ["a", "b"]` is `[(1, "a"), (1, "b"), (2, "a"), (2, "b")]`.
def List.cross (xs: List a) (ys: List b): List (Pair a b) := List.flatMap xs (x => List.map (y => MkPair x y) ys)

theorem List.lengthTails: (xs: List a) -> List.length (List.tails xs) = Succ (List.length xs)
  | Nil       => rfl
  | Cons x xs => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take n xs := rfl

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := rfl

test "List.maxBy" := [MkPair 2 "bb", MkPair 1 "a", MkPair 3 "ccc"].maxBy Pair.fst == Some (MkPair 3 "ccc") && (Nil: List Nat).maxBy (x => x) == None
test "List.maxBy first wins a tie" := [MkPair 1 "a", MkPair 3 "b", MkPair 3 "c"].maxBy Pair.fst == Some (MkPair 3 "b")
test "List.minBy first wins a tie" := [MkPair 3 "z", MkPair 1 "a", MkPair 1 "b"].minBy Pair.fst == Some (MkPair 1 "a") && (Nil: List Nat).minBy (x => x) == None
test "List.takeWhile and dropWhile" := [1, 2, 5, 1].takeWhile (x => Nat.leq x 2) == [1, 2] && [1, 2, 5, 1].dropWhile (x => Nat.leq x 2) == [5, 1]
test "List.takeWhile all and none" := [1, 2].takeWhile (x => Nat.leq x 8) == [1, 2] && [1, 2].dropWhile (x => Nat.leq x 8) == Nil && [4].takeWhile (x => Nat.leq x 2) == Nil
test "List.span" := List.span [1, 2, 5, 1] (x => Nat.leq x 2) == MkPair [1, 2] [5, 1] && List.span (Nil: List Nat) (x => Nat.leq x 2) == MkPair Nil Nil
test "List.splitAt" := [1, 2, 3].splitAt 1 == MkPair [1] [2, 3] && [1, 2].splitAt 5 == MkPair [1, 2] Nil && [1, 2].splitAt 0 == MkPair Nil [1, 2]
test "List.dropRight" := [1, 2, 3, 4].dropRight 1 == [1, 2, 3] && [1, 2].dropRight 5 == Nil && [1, 2].dropRight 0 == [1, 2]
test "List.tails" := [1, 2].tails == [[1, 2], [2], Nil] && (Nil: List Nat).tails == [Nil]
test "List.findIndex" := [5, 6, 7].findIndex (x => Nat.leq 6 x) == Some 1 && [5].findIndex (x => Nat.leq 10 x) == None
test "List.withIndex" := ["a", "b"].withIndex == [MkPair 0 "a", MkPair 1 "b"] && (Nil: List Nat).withIndex == Nil
test "List.findMap" := [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == Some 30 && [1].findMap (x => (None: Option Nat)) == None
test "List.flatMap" := [1, 2, 3].flatMap (x => List.replicate x x) == [1, 2, 2, 3, 3, 3]
test "List.cross" := [1, 2].cross ["a", "b"] == [MkPair 1 "a", MkPair 1 "b", MkPair 2 "a", MkPair 2 "b"] && [1].cross (Nil: List Nat) == Nil
