-- The list toolkit: `map`, `filter`, folds, sums, `zip`, `take`/`drop`, `get`,
-- `splitBy`, padding, transpose and their lemmas. This file was the prelude's
-- "List toolkit" block and the list lemmas beside it.

theorem List.lengthAppend: (xs: List a) → (ys: List a) → List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil, ys => rfl
  | Cons x xs, ys => Eq.cong Succ (List.lengthAppend xs ys)

-- List toolkit. Every function is structurally recursive.
--
-- The callbacks of `map`, `filter`, `foldLeft`, `foldRight`, `sumBy`,
-- `count`, `any`, `all`, `find`, `filterMap`, `findMap`, `takeWhile`,
-- `flatMap`, `partition` and `span` may perform abilities, such as `Fail`,
-- `Log` or `Partial` (docs/proposals/effect-polymorphism.md and
-- effect-polymorphic-list.md). Their types say so with `{e}`: in
-- `p: a → {e} Bool`, `e` is the callback's row, and the result `{e} List a`
-- performs the same. With a pure callback the row is empty and `{e} b` is
-- `b`, so each is the plain function: its lemmas are about that, and the
-- backends compile it to the same loop. The other callbacks (`zipWith`,
-- `scanLeft`, the sorts, …) must be pure. With an effectful callback:
-- - the effects run in list order, first element first (`foldRight`'s run
--   last to first, as its definition reads);
-- - the callback is called at most once per element;
-- - `any`, `all`, `find`, `findMap`, `takeWhile` and `span` stop calling it
--   once the answer is decided.

-- `f` on each element, in order. `f` may perform abilities, such as `Fail`:
-- `xs.map Range.read` fails at the first element that isn't a range
-- (docs/proposals/errors.md §3.4). With a pure `f` the row is empty and
-- `{e} b` is `b`, so this is the plain map: its lemmas are proved by
-- computation as before, and the backends compile it to the same loop.
def List.map: List a → (f: a → {e} b) → {e} List b
  | Nil, f => Nil
  | Cons x xs, f => Cons (f x) (List.map xs f)

-- One step of `List.filter`: `x` in front of the filtered rest, or not. A
-- function of its own so the recursive call is written once: with an `if`
-- around it in both branches, a condition the checker can't decide (one on
-- a variable) keeps both branches, and the value doubles with every element.
@[noReceiver]
def List.filterStep (x: a) (rest: List a): Bool → List a
  | True => Cons x rest
  | False => rest

-- The elements satisfying `p`, in order. `p` may perform abilities: it runs on
-- each element once, in list order (the `let` runs it before the rest of the
-- list is filtered), so a `Fail` reports the first bad element.
def List.filter: List a → (p: a → {e} Bool) → {e} List a
  | Nil, p => Nil
  | Cons x xs, p =>
    let keep := p x
    List.filterStep x (List.filter xs p) keep

-- Left fold; tail-recursive. `List.foldLeft [x, y] initial f` is `f (f initial x) y`.
-- `f` may perform abilities, which run in list order.
def List.foldLeft: List a → (initial: b) → (f: b → a → {e} b) → {e} b
  | Nil, initial, f => initial
  | Cons x xs, initial, f => List.foldLeft xs (f initial x) f

-- Running accumulations, the initial value first (Haskell's `scanLeft`):
-- `List.scanLeft [x, y] initial f` is `[initial, f initial x, f (f initial x) y]`. Always one longer than
-- the input.
def List.scanLeft: List a → (initial: b) → (f: b → a → b) → List b
  | Nil, initial, f => Cons initial Nil
  | Cons x xs, initial, f => Cons initial (List.scanLeft xs (f initial x) f)

theorem List.scanLeftNil: List.scanLeft Nil 5 (acc x => acc + x) = [5] := rfl

theorem List.scanLeftSums: List.scanLeft [1, 2, 3] 0 (acc x => acc + x) = [0, 1, 3, 6] := rfl

-- Right fold. `List.foldRight [x, y] initial f` is `f x (f y initial)`. Runs
-- as a loop over the reversed list, so it is stack-safe on long lists. `f`
-- may perform abilities, which run last element first, as the definition
-- reads: `f y initial` is computed before `f x …`.
def List.foldRight (xs: List a) (initial: b) (f: a → b → {e} b): {e} b := List.foldLeft (List.reverseOnto xs Nil) initial (acc x => f x acc)

theorem List.foldLeftReverseOnto: (xs: List a) → (acc: List a) → (z: b) → (f: a → b → b) →
    List.foldLeft (List.reverseOnto xs acc) z (r x => f x r)
      = List.foldLeft acc (List.foldLeft (List.reverseOnto xs Nil) z (r x => f x r)) (r x => f x r)
  | Nil, acc, z, f => rfl
  | Cons x xs, acc, z, f =>
    Eq.trans (List.foldLeftReverseOnto xs (Cons x acc) z f)
      (Eq.sym (Eq.cong (r => List.foldLeft acc r (r2 y => f y r2)) (List.foldLeftReverseOnto xs (Cons x Nil) z f)))

-- The step of the right fold, which the loop form hides.
theorem List.foldRightCons (xs: List a) (x: a) (z: b) (f: a → b → b): List.foldRight (Cons x xs) z f = f x (List.foldRight xs z f) :=
  List.foldLeftReverseOnto xs (Cons x Nil) z f

-- The sum of the elements, of any type with `Add` (docs/proposals/interfaces.md
-- §7.7): `[1, 2, 3].sum` is `6`, `[3, -5, 1].sum` is `-1`.
def List.sum [auto add: Add a] (xs: List a): a := List.foldLeft xs Add.zero Add.add

-- The sum of `f` over the elements: `List.sumBy xs f` is `List.sum (List.map xs f)`
-- without building the intermediate list. `f` may perform abilities, which
-- run in list order.
def List.sumBy [auto add: Add b] (xs: List a) (f: a → {e} b): {e} b := List.foldLeft xs Add.zero (acc x => acc + f x)

theorem List.sumByDoubles: List.sumBy [1, 2, 3] (x => x * 2) = 12 := rfl

theorem List.sumInts: List.sum [(3: Int), -5, 1] = -1 := rfl

theorem List.sumByInts: List.sumBy [(1: Int), 2, 3] (x => Int.sub 1 x) = -3 := rfl

-- The product of the elements, of any type with `Mul`.
def List.product [auto mul: Mul a] (xs: List a): a := List.foldLeft xs Mul.one Mul.mul

def List.maximum [auto ord: Ord a]: List a → Option a
  | Nil => None
  | Cons x xs => Some (List.foldLeft xs x Ord.max)

def List.minimum [auto ord: Ord a]: List a → Option a
  | Nil => None
  | Cons x xs => Some (List.foldLeft xs x Ord.min)

-- Pairs up to the shorter list's length.
def List.zip: List a → List b → List (Pair a b)
  | Nil, ys => Nil
  | Cons x xs, Nil => Nil
  | Cons x xs, Cons y ys => Cons (MkPair x y) (List.zip xs ys)

def List.zipWith: List a → List b → (f: a → b → c) → List c
  | Nil, ys, f => Nil
  | Cons x xs, Nil, f => Nil
  | Cons x xs, Cons y ys, f => Cons (f x y) (List.zipWith xs ys f)

-- Combines three lists up to the shortest list's length.
def List.zipWith3: List a → List b → List c → (f: a → b → c → d) → List d
  | Nil, ys, zs, f => Nil
  | Cons x xs, Nil, zs, f => Nil
  | Cons x xs, Cons y ys, Nil, f => Nil
  | Cons x xs, Cons y ys, Cons z zs, f => Cons (f x y z) (List.zipWith3 xs ys zs f)

-- The first n elements (all of them if there are fewer).
def List.take: List a → Nat → List a
  | xs, Zero => Nil
  | Nil, Succ n => Nil
  | Cons x xs, Succ n => Cons x (List.take xs n)

-- All but the first n elements.
def List.drop: List a → Nat → List a
  | xs, Zero => xs
  | Nil, Succ n => Nil
  | Cons x xs, Succ n => List.drop xs n

-- The element at index i, counting from 0.
def List.get: List a → Nat → Option a
  | Nil, i => None
  | Cons x xs, Zero => Some x
  | Cons x xs, Succ i => List.get xs i

-- Whether some element satisfies `p`. `p` may perform abilities: it runs in
-- list order and isn't called after the first element that satisfies it.
def List.any: List a → (p: a → {e} Bool) → {e} Bool
  | Nil, p => False
  | Cons x xs, p => if p x then True else List.any xs p

-- Whether every element satisfies `p`. `p` may perform abilities: it runs in
-- list order and isn't called after the first element that fails it.
def List.all: List a → (p: a → {e} Bool) → {e} Bool
  | Nil, p => True
  | Cons x xs, p => if p x then List.all xs p else False

-- `n`, plus one if `b`: `List.count`'s step. A function of its own so `n` is
-- written once: `if b then Succ n else n` writes it twice, so when the
-- checker can't decide the conditions, a count doubles in size with every
-- element.
def Nat.succIf (n: Nat): Bool → Nat
  | True => Succ n
  | False => n

-- How many elements satisfy `p`. `p` may perform abilities, which run in
-- list order.
def List.count (xs: List a) (p: a → {e} Bool): {e} Nat := List.foldLeft xs 0 (n x => Nat.succIf n (p x))

-- The first element satisfying `p`. `p` may perform abilities: it runs in
-- list order and isn't called after the element found.
def List.find: List a → (p: a → {e} Bool) → {e} Option a
  | Nil, p => None
  | Cons x xs, p => if p x then Some x else List.find xs p

@[noReceiver]
def List.consSome: Option b → List b → List b
  | None, rest => rest
  | Some y, rest => Cons y rest

-- Keeps the `Some` results, in order. `f` may perform abilities, which run in
-- list order (`f x` is the first argument, so it runs before the rest).
def List.filterMap: List a → (f: a → {e} Option b) → {e} List b
  | Nil, f => Nil
  | Cons x xs, f => List.consSome (f x) (List.filterMap xs f)

-- Joins a list of lists.
def List.concat: List (List a) → List a
  | Nil => Nil
  | Cons xs xss => List.append xs (List.concat xss)

-- `List.replicate n x` is n copies of x.
def List.replicate: Nat → a → List a
  | Zero, x => Nil
  | Succ n, x => Cons x (List.replicate n x)

def List.rangeFrom: Nat → Nat → List Nat
  | Zero, i => Nil
  | Succ n, i => Cons i (List.rangeFrom n (Succ i))

-- A run of `a + b` numbers is a run of `a` followed by a run of `b`.
theorem List.rangeFromAppend: (a: Nat) → (b: Nat) → (s: Nat) → List.rangeFrom (a + b) s = List.append (List.rangeFrom a s) (List.rangeFrom b (s + a))
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

test "List.lengthBetween" := List.length (List.between 3 3) == 1 ∧ List.length (List.between 5 2) == 0 ∧ List.length (List.between 2 6) == 5
test "List.between, empty and single" := List.between 5 0 == Nil ∧ List.between 0 0 == [0] ∧ List.between 7 7 == [7]

def List.reverse (xs: List a): List a := List.reverseOnto xs Nil

def List.last: List a → Option a
  | Nil => None
  | Cons x Nil => Some x
  | Cons x (Cons y ys) => List.last (Cons y ys)

-- The first element, or `None` for an empty list.
def List.head: List a → Option a
  | Nil => None
  | Cons x xs => Some x

theorem List.headExample: List.head [3, 4] = Some 3 := rfl

theorem List.headEmpty: List.head (Nil: List Nat) = None := rfl

-- All but the last element (`Nil` for an empty list).
def List.init: List a → List a
  | Nil => Nil
  | Cons x Nil => Nil
  | Cons x (Cons y ys) => Cons x (List.init (Cons y ys))

theorem List.initExample: List.init [1, 2, 3] = [1, 2] := rfl

theorem List.initEmpty: List.init (Nil: List Nat) = Nil := rfl

-- Membership, given a decision for equality (as `List.decEq` takes).
def List.elem: List a → (target: a) → (decEq: (x: a) → (y: a) → Decidable (x = y)) → Bool
  | Nil, target, decEq => False
  | Cons x xs, target, decEq => if Decidable.toBool (decEq target x) then True else List.elem xs target decEq

-- One step of `List.partition`: `x` onto the kept or the dropped side of
-- `sides` (each reversed). A function of its own so the recursive call is
-- written once, as for `List.filterStep`.
@[noReceiver]
def List.partitionStep (x: a) (sides: Pair (List a) (List a)): Bool → Pair (List a) (List a)
  | True => MkPair (Cons x (Pair.fst sides)) (Pair.snd sides)
  | False => MkPair (Pair.fst sides) (Cons x (Pair.snd sides))

-- `List.partition`'s loop: `sides` holds what has been sorted so far, each
-- side reversed.
@[noReceiver]
def List.partitionOnto (p: a → {e} Bool): List a → (sides: Pair (List a) (List a)) → {e} Pair (List a) (List a)
  | Nil, sides => MkPair (List.reverse (Pair.fst sides)) (List.reverse (Pair.snd sides))
  | Cons x xs, sides =>
    let keep := p x
    List.partitionOnto p xs (List.partitionStep x sides keep)

-- The elements that satisfy `p`, and those that don't, each in order: the
-- two `filter`s (`List.partitionFilters`) in one pass. `p` may perform
-- abilities: it runs once per element, in list order.
def List.partition (xs: List a) (p: a → {e} Bool): {e} Pair (List a) (List a) := List.partitionOnto p xs (MkPair Nil Nil)

-- The loop's sides are the two `filter`s, each after what it had sorted.
theorem List.partitionOntoFilters (p: a → Bool): (xs: List a) → (kept: List a) → (dropped: List a) →
    List.partitionOnto p xs (MkPair kept dropped)
      = MkPair (List.reverseOnto kept (List.filter xs p)) (List.reverseOnto dropped (List.filter xs (x => ¬(p x))))
  | Nil, kept, dropped => rfl
  | Cons x xs, kept, dropped =>
    match p x with
      | True => List.partitionOntoFilters p xs (Cons x kept) dropped
      | False => List.partitionOntoFilters p xs kept (Cons x dropped)

-- `partition` is the two `filter`s (its definition before it became one pass).
theorem List.partitionFilters (xs: List a) (p: a → Bool): List.partition xs p = MkPair (List.filter xs p) (List.filter xs (x => ¬(p x))) :=
  List.partitionOntoFilters p xs Nil Nil

theorem List.partitionExample: List.partition [1, 5, 2, 7] (x => x > 4) = MkPair [5, 7] [1, 2] := rfl

test "List.partition" := List.partition [1, 5, 2, 7] (x => x > 4) == MkPair [5, 7] [1, 2] ∧ List.partition (Nil: List Nat) (x => x > 4) == MkPair Nil Nil

-- The value for the first pair whose key is equal, given a decision for equality.
def List.lookup: List (Pair k v) → (key: k) → (decEq: (x: k) → (y: k) → Decidable (x = y)) → Option v
  | Nil, key, decEq => None
  | Cons (MkPair k v) rest, key, decEq => if Decidable.toBool (decEq key k) then Some v else List.lookup rest key decEq

-- `List.padRight xs n x` is `xs` followed by enough copies of `x` to make it
-- n long (it is `xs` itself when that is already n long or longer).
def List.padRight (xs: List a) (n: Nat) (x: a): List a := xs.append (List.replicate (n - xs.length) x)

theorem List.lengthReplicate (x: a): (n: Nat) → List.length (List.replicate n x) = n
  | Zero => rfl
  | Succ n => Eq.cong Succ (List.lengthReplicate x n)

-- Padding makes a list exactly n long, when it was no longer than that.
theorem List.padRightLength (xs: List a) (n: Nat) (x: a) (h: List.length xs ≤ n):
    List.length (List.padRight xs n x) = n :=
  Eq.trans (List.lengthAppend xs (List.replicate (n - List.length xs) x))
    (Eq.trans (Eq.cong (t => List.length xs + t) (List.lengthReplicate x (n - List.length xs)))
      (Nat.addSubCancel (List.length xs) n h))

-- The first `n` columns of a list of rows (`List.transpose`'s loop): column i
-- is the i-th element of each row that has one.
@[noReceiver]
def List.transposeN: Nat → List (List a) → List (List a)
  | Zero, rows => Nil
  | Succ n, rows => Cons (List.filterMap rows (.get 0)) (List.transposeN n (List.map rows (.drop 1)))

-- Swaps rows and columns: the columns of a list of rows, as many as the first
-- row is long. For rows that are all the same length, the cell at row r and
-- column c moves to row c and column r. A row that's too short just leaves
-- its column out, and a row longer than the first loses its extra cells: the
-- result has the first row's width, so `[[1], [2, 3]].transpose` is
-- `[[1, 2]]` (Haskell's `transpose` goes to the longest row instead).
def List.transpose (rows: List (List a)): List (List a) := List.transposeN (List.length (List.headOr rows Nil)) rows

theorem List.padRightExample: List.padRight [1, 2] 4 0 = [1, 2, 0, 0] := rfl

theorem List.padRightLongEnough: List.padRight [1, 2] 1 0 = [1, 2] := rfl

-- Lemmas about `List.transpose`: it has as many columns as the first row is
-- long, and for a rectangular list, doing it twice gives back the list.
theorem List.lengthMap: (xs: List a) → (f: a → b) → List.length (List.map xs f) = List.length xs
  | Nil, f => rfl
  | Cons x xs, f => Eq.cong Succ (List.lengthMap xs f)

theorem List.transposeExample: List.transpose [[1, 2, 3], [4, 5, 6]] = [[1, 4], [2, 5], [3, 6]] := rfl

theorem List.transposeNone: List.transpose (Nil: List (List Nat)) = Nil := rfl

theorem List.transposeShortRow: List.transpose [[1, 2], [3], [4, 5]] = [[1, 3, 4], [2, 5]] := rfl

theorem List.transposeNLength: (n: Nat) → (rows: List (List a)) → List.length (List.transposeN n rows) = n
  | Zero, rows => rfl
  | Succ n, rows => Eq.cong Succ (List.transposeNLength n (List.map rows (.drop 1)))

-- Every element of the list satisfies `p`.
@[noReceiver]
def List.All (p: a → Prop): List a → Prop
  | Nil => Unit
  | Cons x xs => And (p x) (List.All p xs)

-- Some element of the list satisfies `p`.
@[noReceiver]
def List.Any (p: a → Prop): List a → Prop
  | Nil => Void
  | Cons x xs => Or (p x) (List.Any p xs)

theorem List.allAppend (p: a → Prop): (xs: List a) → (ys: List a) → List.All p xs → List.All p ys → List.All p (List.append xs ys)
  | Nil, ys, hx, hy => hy
  | Cons x xs, ys, Both hx hxs, hy => Both hx (List.allAppend p xs ys hxs hy)

theorem List.allAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p xs
  | Nil, ys, h => Trivial
  | Cons x xs, ys, Both h hxs => Both h (List.allAppendLeft p xs ys hxs)

theorem List.allAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.All p (List.append xs ys) → List.All p ys
  | Nil, ys, h => h
  | Cons x xs, ys, Both h hxs => List.allAppendRight p xs ys hxs

theorem List.allMap: (xs: List a) → (p: b → Prop) → (f: a → b) → List.All (x => p (f x)) xs → List.All p (List.map xs f)
  | Nil, p, f, h => Trivial
  | Cons x xs, p, f, Both h hxs => Both h (List.allMap xs p f hxs)

theorem List.allImplies (p: a → Prop) (q: a → Prop) (h: (x: a) → p x → q x): (xs: List a) → List.All p xs → List.All q xs
  | Nil, hp => Trivial
  | Cons x xs, Both hpx hpxs => Both (h x hpx) (List.allImplies p q h xs hpxs)

theorem List.anyAppendLeft (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p xs → List.Any p (List.append xs ys)
  | Nil, ys, h => Void.exfalso h
  | Cons x xs, ys, Inl h => Inl h
  | Cons x xs, ys, Inr h => Inr (List.anyAppendLeft p xs ys h)

theorem List.anyAppendRight (p: a → Prop): (xs: List a) → (ys: List a) → List.Any p ys → List.Any p (List.append xs ys)
  | Nil, ys, h => h
  | Cons x xs, ys, h => Inr (List.anyAppendRight p xs ys h)

-- `List.any` of two lists joined: either list has one.
theorem List.anyAppend: (xs: List a) → (ys: List a) → (p: a → Bool) → List.any (List.append xs ys) p = (List.any xs p ∨ List.any ys p)
  | Nil, ys, p => rfl
  | Cons x xs, ys, p =>
    match e: p x with
      | True => rfl
      | False => List.anyAppend xs ys p

theorem List.anyAppendExample: List.any (List.append [1, 2] [3]) (x => x == 3) = (False ∨ True) := rfl

-- Every row has length n (the list is rectangular).
@[noReceiver]
def List.AllLength (n: Nat): List (List a) → Prop
  | Nil => Unit
  | Cons r rs => And (List.length r = n) (List.AllLength n rs)

theorem List.lengthZero: (xs: List a) → List.length xs = 0 → xs = Nil
  | Nil, h => rfl
  | Cons y ys, h => Void.exfalso (Nat.succNotZero (List.length ys) h)

theorem List.transposeNNil: (n: Nat) → List.transposeN n (Nil: List (List a)) = List.replicate n Nil
  | Zero => rfl
  | Succ n => Eq.cong (Cons Nil) (List.transposeNNil n)

theorem List.allLengthZero: (rows: List (List a)) → (n: Nat) → List.length rows = n → List.AllLength 0 rows →
    rows = List.replicate n Nil
  | Nil, n, hl, hr => J (y q => (Nil: List (List a)) = List.replicate y (Nil: List a)) rfl hl
  | Cons r rs, Zero, hl, hr => Void.exfalso (Nat.succNotZero (List.length rs) hl)
  | Cons r rs, Succ m, hl, Both hr hrs =>
    Eq.trans (Eq.cong (t => Cons t rs) (List.lengthZero r hr))
      (Eq.cong (Cons Nil) (List.allLengthZero rs m (Nat.succInjective (List.length rs) m hl) hrs))

theorem List.tailsAllLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.AllLength k (List.map rows (.drop 1))
  | Nil, k, hr => Trivial
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Both (Nat.succInjective (List.length ys) k hr) (List.tailsAllLength rs k hrs)

theorem List.headsLength: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    List.length (List.filterMap rows (.get 0)) = List.length rows
  | Nil, k, hr => rfl
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Eq.cong Succ (List.headsLength rs k hrs)

theorem List.rowsAreHeadsAndTails: (rows: List (List a)) → (k: Nat) → List.AllLength (Succ k) rows →
    rows = List.zipWith (List.filterMap rows (.get 0)) (List.map rows (.drop 1)) Cons
  | Nil, k, hr => rfl
  | Cons Nil rs, k, Both hr hrs => Void.exfalso (Nat.zeroNotSucc k hr)
  | Cons (Cons y ys) rs, k, Both hr hrs => Eq.cong (Cons (Cons y ys)) (List.rowsAreHeadsAndTails rs k hrs)

theorem List.columnsAllLength: (w: Nat) → (rows: List (List a)) → (h: Nat) → List.length rows = h → List.AllLength w rows →
    List.AllLength h (List.transposeN w rows)
  | Zero, rows, h, hl, hr => Trivial
  | Succ k, rows, h, hl, hr =>
    Both (Eq.trans (List.headsLength rows k hr) hl)
      (List.columnsAllLength k (List.map rows (.drop 1)) h (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr))

theorem List.transposeNCons: (heads: List a) → (h: Nat) → (cols: List (List a)) → List.length heads = h → List.AllLength h cols →
    List.transposeN h (Cons heads cols) = List.zipWith heads (List.transposeN h cols) Cons
  | Nil, Zero, cols, hl, hc => rfl
  | Cons x xs, Zero, cols, hl, hc => Void.exfalso (Nat.succNotZero (List.length xs) hl)
  | Nil, Succ m, cols, hl, hc => Void.exfalso (Nat.zeroNotSucc m hl)
  | Cons x xs, Succ m, cols, hl, hc =>
    Eq.cong (Cons (Cons x (List.filterMap cols (.get 0))))
      (List.transposeNCons xs m (List.map cols (.drop 1)) (Nat.succInjective (List.length xs) m hl) (List.tailsAllLength cols m hc))

theorem List.transposeNTwice: (w: Nat) → (h: Nat) → (rows: List (List a)) → List.length rows = h → List.AllLength w rows →
    List.transposeN h (List.transposeN w rows) = rows
  | Zero, h, rows, hl, hr => Eq.trans (List.transposeNNil h) (Eq.sym (List.allLengthZero rows h hl hr))
  | Succ k, h, rows, hl, hr =>
    Eq.trans
      (List.transposeNCons (List.filterMap rows (.get 0)) h (List.transposeN k (List.map rows (.drop 1)))
        (Eq.trans (List.headsLength rows k hr) hl)
        (List.columnsAllLength k (List.map rows (.drop 1)) h (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr)))
      (Eq.trans
        (Eq.cong (tails => List.zipWith (List.filterMap rows (.get 0)) tails Cons)
          (List.transposeNTwice k h (List.map rows (.drop 1)) (Eq.trans (List.lengthMap rows (.drop 1)) hl) (List.tailsAllLength rows k hr)))
        (Eq.sym (List.rowsAreHeadsAndTails rows k hr)))

-- There are as many columns as the first row is long.
theorem List.transposeLength (rows: List (List a)): List.length (List.transpose rows) = List.length (List.headOr rows Nil) :=
  List.transposeNLength (List.length (List.headOr rows Nil)) rows

-- Transposing a rectangular list (every row the same non-zero length) twice
-- gives the list back. (With rows of length 0, the first transpose is empty
-- and the rows are lost.)
theorem List.transposeTwice (k: Nat): (rows: List (List a)) → List.AllLength (Succ k) rows →
    List.transpose (List.transpose rows) = rows
  | Nil, hr => rfl
  | Cons r rs, Both hr hrs =>
    J (y q => List.transposeN (List.length (List.headOr (List.transposeN y (Cons r rs)) Nil)) (List.transposeN y (Cons r rs)) = Cons r rs)
      (List.transposeNTwice (Succ k) (List.length (List.headOr (List.transposeN (Succ k) (Cons r rs)) Nil)) (Cons r rs)
        (Eq.sym (List.headsLength (Cons r rs) k (Both hr hrs))) (Both hr hrs))
      (Eq.sym hr)

-- The groups of consecutive elements that don't satisfy `p`, in order: `p`
-- marks the separators, which are dropped, and no group is empty. So
-- `List.splitBy [1, 2, 0, 0, 3] (x => x == 0)` is `[[1, 2], [3]]`.
def List.splitBy (xs: List a) (p: a → Bool): List (List a) := List.finishGroups (List.splitGroups xs p)

-- Reads the list from the right: the group still open at the front, and the
-- groups finished after it. A right fold, so it runs as a loop over the
-- reversed list (stack-safe on long lists); `List.splitGroupsCons` is its step.
def List.splitGroups (xs: List a) (p: a → Bool): Pair (List a) (List (List a)) :=
  List.foldRight xs (MkPair Nil Nil) (x st => List.splitStep x (p x) st)

-- Adds the element `x` in front: a separator (`True`) closes the open group,
-- anything else joins it.
def List.splitStep (x: a): Bool → Pair (List a) (List (List a)) → Pair (List a) (List (List a))
  | True, MkPair cur done => MkPair Nil (List.closeGroup cur done)
  | False, MkPair cur done => MkPair (Cons x cur) done

def List.finishGroups: Pair (List a) (List (List a)) → List (List a)
  | MkPair cur done => List.closeGroup cur done

-- The step of `List.splitGroups`, which the loop form hides.
theorem List.splitGroupsCons (xs: List a) (x: a) (p: a → Bool):
    List.splitGroups (Cons x xs) p = List.splitStep x (p x) (List.splitGroups xs p) :=
  List.foldRightCons xs x (MkPair Nil Nil) (y st => List.splitStep y (p y) st)

-- Adds a group to the finished ones, unless it is empty.
def List.closeGroup: List a → List (List a) → List (List a)
  | Nil, done => done
  | Cons y ys, done => Cons (Cons y ys) done

def List.splitTotal (st: Pair (List a) (List (List a))): Nat := List.length (Pair.fst st) + List.sumBy (Pair.snd st) List.length

theorem List.closeGroupSum: (cur: List a) → (done: List (List a)) →
    List.sumBy (List.closeGroup cur done) List.length = List.length cur + List.sumBy done List.length
  | Nil, done => rfl
  | Cons y ys, done => List.sumByCons done (Cons y ys) List.length

theorem List.splitStepTotal (x: a): (b: Bool) → (st: Pair (List a) (List (List a))) →
    List.splitTotal (List.splitStep x b st) + Bool.toNat b = Succ (List.splitTotal st)
  | True, MkPair cur done =>
    Eq.trans (Nat.addOne (List.sumBy (List.closeGroup cur done) List.length)) (Eq.cong Succ (List.closeGroupSum cur done))
  | False, MkPair cur done => Nat.addZero (Succ (List.length cur + List.sumBy done List.length))

theorem List.splitGroupsTotal: (xs: List a) → (p: a → Bool) →
    List.splitTotal (List.splitGroups xs p) + List.occurrences xs p = List.length xs
  | Nil, p => rfl
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in
      Eq.trans (Eq.sym (Nat.addAssoc (List.splitTotal (List.splitStep x (p x) (List.splitGroups xs p))) (Bool.toNat (p x)) (List.occurrences xs p)))
        (Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.splitStepTotal x (p x) (List.splitGroups xs p)))
          (Eq.cong Succ (List.splitGroupsTotal xs p)))

theorem List.finishGroupsSum: (st: Pair (List a) (List (List a))) →
    List.sumBy (List.finishGroups st) List.length = List.splitTotal st
  | MkPair cur done => List.closeGroupSum cur done

-- The groups hold every element that isn't a separator, and nothing else.
theorem List.splitByExample: List.splitBy [1, 2, 0, 0, 3] (x => x == 0) = [[1, 2], [3]] := rfl

theorem List.splitByEdges: List.splitBy [0, 4, 0] (x => x == 0) = [[4]] := rfl

-- Splitting loses only the separators: the groups' lengths plus the number of separators is the length.
theorem List.splitByLength (xs: List a) (p: a → Bool):
    List.sumBy (List.splitBy xs p) List.length + List.occurrences xs p = List.length xs :=
  Eq.trans (Eq.cong (t => t + List.occurrences xs p) (List.finishGroupsSum (List.splitGroups xs p))) (List.splitGroupsTotal xs p)

-- The group has no separator in it.
@[noReceiver]
def List.NonSep (p: a → Bool) (g: List a): Prop := List.all g (x => ¬(p x)) = True

-- Every group is non-empty and has no separator in it.
@[noReceiver]
def List.Groups (p: a → Bool): List (List a) → Prop
  | Nil => Unit
  | Cons g gs => And (And (0 < List.length g) (List.NonSep p g)) (List.Groups p gs)

def List.SplitOk (p: a → Bool): Pair (List a) (List (List a)) → Prop
  | MkPair cur done => And (List.NonSep p cur) (List.Groups p done)

theorem List.closeGroupGroups (p: a → Bool): (cur: List a) → (done: List (List a)) → List.NonSep p cur → List.Groups p done →
    List.Groups p (List.closeGroup cur done)
  | Nil, done, hc, hd => hd
  | Cons y ys, done, hc, hd => Both (Both (Nat.zeroLe (List.length ys)) hc) hd

theorem List.nonSepCons (p: a → Bool) (x: a) (cur: List a) (h: p x = False) (hc: List.NonSep p cur): List.NonSep p (Cons x cur) :=
  rewrite h in hc

theorem List.splitStepOk (p: a → Bool) (x: a): (b: Bool) → p x = b → (st: Pair (List a) (List (List a))) → List.SplitOk p st →
    List.SplitOk p (List.splitStep x b st)
  | True, e, MkPair cur done, Both hc hd => Both rfl (List.closeGroupGroups p cur done hc hd)
  | False, e, MkPair cur done, Both hc hd => Both (List.nonSepCons p x cur e hc) hd

theorem List.splitGroupsOk: (xs: List a) → (p: a → Bool) → List.SplitOk p (List.splitGroups xs p)
  | Nil, p => Both rfl Trivial
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in List.splitStepOk p x (p x) rfl (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.finishGroupsOk (p: a → Bool): (st: Pair (List a) (List (List a))) → List.SplitOk p st → List.Groups p (List.finishGroups st)
  | MkPair cur done, Both hc hd => List.closeGroupGroups p cur done hc hd

-- No group is empty, and none has a separator in it.
theorem List.splitByGroups (xs: List a) (p: a → Bool): List.Groups p (List.splitBy xs p) :=
  List.finishGroupsOk p (List.splitGroups xs p) (List.splitGroupsOk xs p)

theorem List.closeGroupConcat: (cur: List a) → (done: List (List a)) →
    List.concat (List.closeGroup cur done) = List.append cur (List.concat done)
  | Nil, done => rfl
  | Cons y ys, done => rfl

@[noReceiver]
def List.SplitKeeps (p: a → Bool) (xs: List a) (st: Pair (List a) (List (List a))): Prop :=
  List.append (Pair.fst st) (List.concat (Pair.snd st)) = List.filter xs (x => ¬(p x))

theorem List.splitStepKeeps (p: a → Bool) (x: a) (xs: List a): (b: Bool) → p x = b → (st: Pair (List a) (List (List a))) →
    List.SplitKeeps p xs st → List.SplitKeeps p (Cons x xs) (List.splitStep x b st)
  | True, e, MkPair cur done, h =>
    Eq.trans (List.closeGroupConcat cur done)
      (Eq.trans h (Eq.sym (List.filterSkip xs (z => ¬(p z)) x (Eq.cong Bool.not e))))
  | False, e, MkPair cur done, h =>
    Eq.trans (Eq.cong (Cons x) h) (Eq.sym (List.filterKeep xs (z => ¬(p z)) x (Eq.cong Bool.not e)))

theorem List.splitGroupsKeeps: (xs: List a) → (p: a → Bool) → List.SplitKeeps p xs (List.splitGroups xs p)
  | Nil, p => rfl
  | Cons x xs, p =>
    rewrite List.splitGroupsCons xs x p in List.splitStepKeeps p x xs (p x) rfl (List.splitGroups xs p) (List.splitGroupsKeeps xs p)

theorem List.finishGroupsConcat: (st: Pair (List a) (List (List a))) →
    List.concat (List.finishGroups st) = List.append (Pair.fst st) (List.concat (Pair.snd st))
  | MkPair cur done => List.closeGroupConcat cur done

-- Joining the groups gives back the elements that aren't separators, in order.
theorem List.splitByConcat (xs: List a) (p: a → Bool):
    List.concat (List.splitBy xs p) = List.filter xs (x => ¬(p x)) :=
  Eq.trans (List.finishGroupsConcat (List.splitGroups xs p)) (List.splitGroupsKeeps xs p)

-- Only separators: no group, open or finished.
theorem List.splitGroupsSeparators: (ys: List a) → (p: a → Bool) → List.all ys p = True → List.splitGroups ys p = MkPair Nil Nil
  | Nil, p, h => rfl
  | Cons y ys, p, h =>
    match e: p y with
      | True => rewrite List.splitGroupsCons ys y p, e, List.splitGroupsSeparators ys p h
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.splitGroupsAppendSeparators (ys: List a) (p: a → Bool) (h: List.all ys p = True): (xs: List a) →
    List.splitGroups (List.append xs ys) p = List.splitGroups xs p
  | Nil => List.splitGroupsSeparators ys p h
  | Cons x xs => rewrite List.splitGroupsCons (List.append xs ys) x p, List.splitGroupsCons xs x p, List.splitGroupsAppendSeparators ys p h xs

-- Separators on the end change no group: `[1, 0, 0]` splits as `[1]` does.
theorem List.splitByAppendSeparators (xs: List a) (p: a → Bool) (ys: List a) (h: List.all ys p = True):
    List.splitBy (List.append xs ys) p = List.splitBy xs p :=
  Eq.cong List.finishGroups (List.splitGroupsAppendSeparators ys p h xs)

test "List.splitBy with separators on the end" :=
  [1, 0, 2].splitBy (== 0) == [[1], [2]] ∧ [1, 0, 2, 0, 0].splitBy (== 0) == [[1], [2]] ∧ [0, 0].splitBy (== 0) == Nil

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

theorem List.sumByFrom [auto add: Add b]: (xs: List a) → (z: b) → (f: a → b) → List.foldLeft xs z (acc x => acc + f x) = z + List.sumBy xs f
  | Nil, z, f => Eq.sym (Add.addZero z)
  | Cons x xs, z, f =>
    calc List.foldLeft xs (z + f x) (acc x => acc + f x)
      _ = (z + f x) + List.sumBy xs f := List.sumByFrom xs (z + f x) f
      _ = z + (f x + List.sumBy xs f) := add.assoc z (f x) (List.sumBy xs f)
      _ = z + List.foldLeft xs (f x) (acc x => acc + f x) := Eq.cong (t => z + t) (Eq.sym (List.sumByFrom xs (f x) f))
      _ = z + List.sumBy (Cons x xs) f := Eq.cong (t => z + List.foldLeft xs t (acc x => acc + f x)) (Eq.sym (add.zeroAdd (f x)))

theorem List.sumByCons [auto add: Add b] (xs: List a) (x: a) (f: a → b): List.sumBy (Cons x xs) f = f x + List.sumBy xs f :=
  Eq.trans (Eq.cong (t => List.foldLeft xs t (acc x => acc + f x)) (add.zeroAdd (f x))) (List.sumByFrom xs (f x) f)

theorem List.sumByAppend [auto add: Add b] (xs: List a) (ys: List a) (f: a → b): List.sumBy (List.append xs ys) f = List.sumBy xs f + List.sumBy ys f :=
  Eq.trans (List.foldLeftAppend xs Add.zero ys (acc x => acc + f x)) (List.sumByFrom ys (List.sumBy xs f) f)

theorem List.filterKeep (xs: List a) (p: a → Bool) (x: a) (h: p x = True): List.filter (Cons x xs) p = Cons x (List.filter xs p) :=
  J (c q => List.filterStep x (List.filter xs p) c = Cons x (List.filter xs p)) rfl (Eq.sym h)

theorem List.filterSkip (xs: List a) (p: a → Bool) (x: a) (h: p x = False): List.filter (Cons x xs) p = List.filter xs p :=
  J (c q => List.filterStep x (List.filter xs p) c = List.filter xs p) rfl (Eq.sym h)

theorem List.foldLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.foldLeft (List.append xs ys) z f = List.foldLeft ys (List.foldLeft xs z f) f
  | Nil, z, ys, f => rfl
  | Cons x xs, z, ys, f => List.foldLeftAppend xs (f z x) ys f

-- Appending and taking; sums of `Nat.keepIf` terms, which pick out some
-- elements; swapping two sums; sums and `any` over a run `s .. s + c` that
-- pick nothing or exactly one element.
theorem List.appendNil: (xs: List a) → List.append xs Nil = xs
  | Nil => rfl
  | Cons x xs => Eq.cong (Cons x) (List.appendNil xs)

theorem List.appendAssoc: (xs: List a) → (ys: List a) → (zs: List a) → List.append (List.append xs ys) zs = List.append xs (List.append ys zs)
  | Nil, ys, zs => rfl
  | Cons x xs, ys, zs => Eq.cong (Cons x) (List.appendAssoc xs ys zs)

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
def List.occurrences: List a → (p: a → Bool) → Nat
  | Nil, p => 0
  | Cons x xs, p => Bool.toNat (p x) + List.occurrences xs p

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

-- Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate (a: Nat) (b: Nat) (c: Nat): (a + b) + c = b + (a + c) := Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm (a: Nat) (b: Nat) (c: Nat): a + (b + c) = b + (a + c) := Eq.trans (Eq.sym (Nat.addAssoc a b c)) (Nat.addRotate a b c)

theorem List.countStep: (b: Bool) → (k: Nat) → (o: Nat) → Nat.succIf k b + o = k + (Bool.toNat b + o)
  | True, k, o => Eq.sym (Nat.addSucc k o)
  | False, k, o => rfl

theorem List.countFold: (xs: List a) → (k: Nat) → (p: a → Bool) →
    List.foldLeft xs k (n x => Nat.succIf n (p x)) = k + List.occurrences xs p
  | Nil, k, p => Eq.sym (Nat.addZero k)
  | Cons x xs, k, p => Eq.trans (List.countFold xs (Nat.succIf k (p x)) p) (List.countStep (p x) k (List.occurrences xs p))

theorem List.countOccurrences (xs: List a) (p: a → Bool): List.count xs p = List.occurrences xs p := List.countFold xs 0 p

theorem List.occurrencesSumBy: (xs: List a) → (p: a → Bool) → List.occurrences xs p = List.sumBy xs (x => Bool.toNat (p x))
  | Nil, p => rfl
  | Cons x xs, p => rewrite List.sumByCons xs x (x => Bool.toNat (p x)), List.occurrencesSumBy xs p

-- A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy (xs: List a) (p: a → Bool): List.count xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  Eq.trans (List.countOccurrences xs p) (List.occurrencesSumBy xs p)

theorem List.occurrencesAppend: (xs: List a) → (ys: List a) → (p: a → Bool) →
    List.occurrences (List.append xs ys) p = List.occurrences xs p + List.occurrences ys p
  | Nil, ys, p => rfl
  | Cons x xs, ys, p =>
    Eq.trans (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend xs ys p))
      (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences ys p)))

theorem List.countNil (p: a → Bool): List.count Nil p = 0 := rfl

theorem List.countCons (xs: List a) (x: a) (p: a → Bool): List.count (Cons x xs) p = Bool.toNat (p x) + List.count xs p :=
  Eq.trans (List.countOccurrences (Cons x xs) p) (Eq.cong (n => Bool.toNat (p x) + n) (Eq.sym (List.countOccurrences xs p)))

theorem List.countAppend (xs: List a) (ys: List a) (p: a → Bool): List.count (List.append xs ys) p = List.count xs p + List.count ys p :=
  Eq.trans (List.countOccurrences (List.append xs ys) p)
    (Eq.trans (List.occurrencesAppend xs ys p)
      (Eq.trans (Eq.cong (n => n + List.occurrences ys p) (Eq.sym (List.countOccurrences xs p)))
        (Eq.cong (n => List.count xs p + n) (Eq.sym (List.countOccurrences ys p)))))

theorem List.scanLeftCons: (xs: List a) → (z: b) → (f: b → a → b) → List.scanLeft xs z f = Cons z (List.drop (List.scanLeft xs z f) 1)
  | Nil, z, f => rfl
  | Cons x xs, z, f => rfl

theorem List.scanLeftAppend: (xs: List a) → (z: b) → (ys: List a) → (f: b → a → b) →
    List.drop (List.scanLeft (List.append xs ys) z f) 1 = List.append (List.drop (List.scanLeft xs z f) 1) (List.drop (List.scanLeft ys (List.foldLeft xs z f) f) 1)
  | Nil, z, ys, f => rfl
  | Cons x xs, z, ys, f =>
    Eq.trans (List.scanLeftCons (List.append xs ys) (f z x) f)
      (Eq.trans (Eq.cong (Cons (f z x)) (List.scanLeftAppend xs (f z x) ys f))
        (Eq.cong (l => List.append l (List.drop (List.scanLeft ys (List.foldLeft xs (f z x) f) f) 1)) (Eq.sym (List.scanLeftCons xs (f z x) f))))

-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
def List.Perm (xs: List a) (ys: List a): Prop := (p: a → Bool) → List.occurrences xs p = List.occurrences ys p

theorem List.permRefl (xs: List a): List.Perm xs xs := p => rfl

theorem List.permSym (xs: List a) (ys: List a) (h: List.Perm xs ys): List.Perm ys xs := p => Eq.sym (h p)

theorem List.permTrans (xs: List a) (ys: List a) (zs: List a) (h1: List.Perm xs ys) (h2: List.Perm ys zs): List.Perm xs zs := p => Eq.trans (h1 p) (h2 p)

theorem List.occurrencesTrue: (xs: List a) → List.occurrences xs (x => True) = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.occurrencesTrue xs)

theorem List.permLength (xs: List a) (ys: List a) (h: List.Perm xs ys): List.length xs = List.length ys := Eq.trans (Eq.sym (List.occurrencesTrue xs)) (Eq.trans (h (x => True)) (List.occurrencesTrue ys))

-- Some element passes `p` exactly when at least one does, so permutations
-- agree on `any`.
theorem List.anyOccurrences: (xs: List a) → (p: a → Bool) → List.any xs p = Nat.leq 1 (List.occurrences xs p)
  | Nil, p => rfl
  | Cons x xs, p =>
    Bool.inspect (p x) (c => Bool.ifThenElse c (u => True) (u => List.any xs p) = Nat.leq 1 (Bool.toNat c + List.occurrences xs p))
      (t => rfl) (f => List.anyOccurrences xs p)

theorem List.anyPerm (xs: List a) (ys: List a) (h: List.Perm xs ys) (p: a → Bool): List.any xs p = List.any ys p :=
  Eq.trans (List.anyOccurrences xs p) (Eq.trans (Eq.cong (n => Nat.leq 1 n) (h p)) (Eq.sym (List.anyOccurrences ys p)))

-- Reversing is a permutation, and keeps sums.
theorem List.occurrencesReverseOnto: (xs: List a) → (acc: List a) → (p: a → Bool) →
    List.occurrences (List.reverseOnto xs acc) p = List.occurrences xs p + List.occurrences acc p
  | Nil, acc, p => rfl
  | Cons x xs, acc, p =>
    Eq.trans (List.occurrencesReverseOnto xs (Cons x acc) p)
      (Eq.trans (Nat.addLeftComm (List.occurrences xs p) (Bool.toNat (p x)) (List.occurrences acc p))
        (Eq.sym (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences acc p))))

theorem List.reversePerm (xs: List a): List.Perm (List.reverse xs) xs := p =>
  Eq.trans (List.occurrencesReverseOnto xs Nil p) (Nat.addZero (List.occurrences xs p))

theorem List.sumByReverseOnto: (xs: List a) → (acc: List a) → (f: a → Nat) →
    List.sumBy (List.reverseOnto xs acc) f = List.sumBy xs f + List.sumBy acc f
  | Nil, acc, f => rfl
  | Cons x xs, acc, f =>
    Eq.trans (List.sumByReverseOnto xs (Cons x acc) f)
      (Eq.trans (Eq.cong (t => List.sumBy xs f + t) (List.sumByCons acc x f))
        (Eq.trans (Nat.addLeftComm (List.sumBy xs f) (f x) (List.sumBy acc f))
          (Eq.trans (Eq.sym (Nat.addAssoc (f x) (List.sumBy xs f) (List.sumBy acc f)))
            (Eq.cong (t => t + List.sumBy acc f) (Eq.sym (List.sumByCons xs x f))))))

theorem List.sumByReverse (xs: List a) (f: a → Nat): List.sumBy (List.reverse xs) f = List.sumBy xs f :=
  Eq.trans (List.sumByReverseOnto xs Nil f) (Nat.addZero (List.sumBy xs f))

-- Counting with a test nothing passes, and with either of two tests.
theorem List.occurrencesNone: (xs: List a) → (p: a → Bool) → (h: (x: a) → p x = False) → List.occurrences xs p = 0
  | Nil, p, h => rfl
  | Cons x xs, p, h => Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p) (h x)) (List.occurrencesNone xs p h)

-- When nothing passes both `p` and `q`, the elements passing either are those
-- passing `p` plus those passing `q`.
theorem List.occurrencesOr: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = False) →
    List.occurrences xs (x => p x ∨ q x) = List.occurrences xs p + List.occurrences xs q
  | Nil, p, q, h => rfl
  | Cons x xs, p, q, h =>
    Bool.inspect (p x)
      (c => Bool.toNat (c ∨ q x) + List.occurrences xs (x => p x ∨ q x)
        = (Bool.toNat c + List.occurrences xs p) + (Bool.toNat (q x) + List.occurrences xs q))
      (t => Eq.trans (Eq.cong (n => 1 + n) (List.occurrencesOr xs p q h))
        (Eq.cong (b => (1 + List.occurrences xs p) + (Bool.toNat b + List.occurrences xs q)) (Eq.sym (h x t))))
      (f => Eq.trans (Eq.cong (n => Bool.toNat (q x) + n) (List.occurrencesOr xs p q h))
        (Nat.addLeftComm (Bool.toNat (q x)) (List.occurrences xs p) (List.occurrences xs q)))

-- `s` is `xs` with some elements left out, the rest kept in order: each
-- element of `s` is matched with an element of `xs`, or `xs`'s first element
-- is skipped.
def List.Subsequence: List a → List a → Prop
  | Nil, ys => Unit
  | Cons x xs, Nil => Void
  | Cons x xs, Cons y ys => Or (And (x = y) (List.Subsequence xs ys)) (List.Subsequence (Cons x xs) ys)

-- Lemmas for proofs about grids: runs' lengths, `map` and `filterMap` fused,
-- `init`, `last` and `reverse` of a `map`, and transposing a grid given cell
-- by cell.
theorem List.lengthRangeFrom: (n: Nat) → (s: Nat) → List.length (List.rangeFrom n s) = n
  | Zero, s => rfl
  | Succ n, s => rewrite List.lengthRangeFrom n (Succ s)

theorem List.mapMap: (xs: List a) → (f: b → c) → (g: a → b) → List.map (List.map xs g) f = List.map xs (x => f (g x))
  | Nil, f, g => rfl
  | Cons x xs, f, g => rewrite List.mapMap xs f g

theorem List.filterMapMap: (xs: List a) → (f: b → Option c) → (g: a → b) → List.filterMap (List.map xs g) f = List.filterMap xs (x => f (g x))
  | Nil, f, g => rfl
  | Cons x xs, f, g => rewrite List.filterMapMap xs f g

theorem List.filterMapSome: (xs: List a) → (f: a → b) → List.filterMap xs (x => Some (f x)) = List.map xs f
  | Nil, f => rfl
  | Cons x xs, f => rewrite List.filterMapSome xs f

theorem List.filterMapAppend: (xs: List a) → (ys: List a) → (f: a → Option b) →
    List.filterMap (List.append xs ys) f = List.append (List.filterMap xs f) (List.filterMap ys f)
  | Nil, ys, f => rfl
  | Cons x xs, ys, f =>
    match f x with
      | None => List.filterMapAppend xs ys f
      | Some y => rewrite List.filterMapAppend xs ys f

theorem List.initMap: (xs: List a) → (f: a → b) → List.init (List.map xs f) = List.map (List.init xs) f
  | Nil, f => rfl
  | Cons x Nil, f => rfl
  | Cons x (Cons y ys), f => rewrite List.initMap (Cons y ys) f

theorem List.lastMap: (xs: List a) → (f: a → b) → List.last (List.map xs f) = Option.map (List.last xs) f
  | Nil, f => rfl
  | Cons x Nil, f => rfl
  | Cons x (Cons y ys), f => List.lastMap (Cons y ys) f
theorem List.mapRangeShift (f: Nat → b): (n: Nat) → (s: Nat) →
    List.map (List.rangeFrom n (Succ s)) f = List.map (List.rangeFrom n s) (i => f (Succ i))
  | Zero, s => rfl
  | Succ n, s => rewrite List.mapRangeShift f n (Succ s)

-- Transposing a grid given cell by cell: row x, column y becomes row y, column x.
theorem List.transposeNGrid (rows: List a): (cols: List b) → (cell: a → b → c) →
    List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x))) = List.map cols (y => List.map rows (x => cell x y))
  | Nil, cell => rfl
  | Cons y cols, cell =>
    calc List.transposeN (Succ (List.length cols)) (List.map rows (x => List.map (Cons y cols) (cell x)))
      _ = Cons (List.filterMap (List.map rows (x => List.map (Cons y cols) (cell x))) (.get 0))
        (List.transposeN (List.length cols) (List.map (List.map rows (x => List.map (Cons y cols) (cell x))) (.drop 1)))
      _ = Cons (List.filterMap rows (x => Some (cell x y))) (List.transposeN (List.length cols) (List.map rows (x => List.map cols (cell x))))
        := rewrite List.filterMapMap rows (.get 0) (x => List.map (Cons y cols) (cell x)),
          List.mapMap rows (.drop 1) (x => List.map (Cons y cols) (cell x))
      _ = Cons (List.map rows (x => cell x y)) (List.map cols (z => List.map rows (x => cell x z)))
        := rewrite List.filterMapSome rows (x => cell x y), List.transposeNGrid rows cols cell

theorem List.transposeGrid (rows: List a) (r: a) (cols: List b) (cell: a → b → c):
    List.transpose (List.map (Cons r rows) (x => List.map cols (cell x))) = List.map cols (y => List.map (Cons r rows) (x => cell x y)) :=
  calc List.transpose (List.map (Cons r rows) (x => List.map cols (cell x)))
    _ = List.transposeN (List.length (List.map cols (cell r))) (List.map (Cons r rows) (x => List.map cols (cell x)))
    _ = List.transposeN (List.length cols) (List.map (Cons r rows) (x => List.map cols (cell x))) := rewrite List.lengthMap cols (cell r)
    _ = List.map cols (y => List.map (Cons r rows) (x => cell x y)) := List.transposeNGrid (Cons r rows) cols cell

theorem List.mapReverseOnto: (xs: List a) → (acc: List a) → (f: a → b) →
    List.map (List.reverseOnto xs acc) f = List.reverseOnto (List.map xs f) (List.map acc f)
  | Nil, acc, f => rfl
  | Cons x xs, acc, f => List.mapReverseOnto xs (Cons x acc) f

theorem List.mapReverse (xs: List a) (f: a → b): List.map (List.reverse xs) f = List.reverse (List.map xs f) := List.mapReverseOnto xs Nil f

-- Congruence lemmas: given callbacks that agree on every argument, a function
-- gives the same result. Their shape is fixed, since `decreasing` looks them up
-- by name (`F` + `Cong`) to follow a recursive call inside a callback
-- (docs/proposals/well-founded-recursion.md, stage 3a): `F`'s parameters in
-- order, each callback twice, then `(x…) -> f1 x… = f2 x…` for each.
theorem List.mapCong: (xs: List a) → (f1: a → b) → (f2: a → b) → ((x: a) → f1 x = f2 x) → List.map xs f1 = List.map xs f2
  | Nil, f1, f2, ef => rfl
  | Cons x xs, f1, f2, ef => Eq.trans (Eq.cong (y => Cons y (List.map xs f1)) (ef x)) (Eq.cong (ys => Cons (f2 x) ys) (List.mapCong xs f1 f2 ef))

theorem List.filterMapCong: (xs: List a) → (f1: a → Option b) → (f2: a → Option b) → ((x: a) → f1 x = f2 x) → List.filterMap xs f1 = List.filterMap xs f2
  | Nil, f1, f2, ef => rfl
  | Cons x xs, f1, f2, ef => rewrite ef x, List.filterMapCong xs f1 f2 ef

theorem List.findCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.find xs p1 = List.find xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x, List.findCong xs p1 p2 ep

theorem List.occurrencesCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) →
    List.occurrences xs p1 = List.occurrences xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep =>
    Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p1) (ep x))
      (Eq.cong (n => Bool.toNat (p2 x) + n) (List.occurrencesCong xs p1 p2 ep))

theorem List.foldLeftCong: (xs: List a) → (z: b) → (f1: b → a → b) → (f2: b → a → b) → ((acc: b) → (x: a) → f1 acc x = f2 acc x) →
    List.foldLeft xs z f1 = List.foldLeft xs z f2
  | Nil, z, f1, f2, ef => rfl
  | Cons x xs, z, f1, f2, ef => Eq.trans (Eq.cong (t => List.foldLeft xs t f1) (ef z x)) (List.foldLeftCong xs (f2 z x) f1 f2 ef)

theorem List.sumByCong [auto add: Add b] (xs: List a) (f1: a → b) (f2: a → b) (ef: (x: a) → f1 x = f2 x): List.sumBy xs f1 = List.sumBy xs f2 :=
  List.foldLeftCong xs Add.zero (acc x => acc + f1 x) (acc x => acc + f2 x) (acc x => Eq.cong (t => acc + t) (ef x))

theorem Option.flatMapMap: (m: Option a) → (g: b → Option c) → (f: a → b) → Option.flatMap (Option.map m f) g = Option.flatMap m (x => g (f x))
  | None, g, f => rfl
  | Some x, g, f => rfl

theorem List.lengthZipWith3 (f: a → b → c → e): (xs: List a) → (ys: List b) → (zs: List c) →
    List.length ys = List.length xs → List.length zs = List.length xs → List.length (List.zipWith3 xs ys zs f) = List.length xs
  | Nil, ys, zs, h1, h2 => rfl
  | Cons x xs, Nil, zs, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h1)
  | Cons x xs, Cons y ys, Nil, h1, h2 => Void.exfalso (Nat.zeroNotSucc (List.length xs) h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    rewrite List.lengthZipWith3 f xs ys zs (Nat.succInjective (List.length ys) (List.length xs) h1) (Nat.succInjective (List.length zs) (List.length xs) h2)

-- A sum over a list is the sum over its indices.

-- `x` is an element of the list.
@[noReceiver]
def List.Mem (x: a) (xs: List a): Prop := List.Any (y => y = x) xs

-- Decides `x ∈ xs` one element at a time from the front, so `x ∈ xs` is a
-- `Bool` where one is expected (`if x ∈ seen`) and `if h: x ∈ xs` names
-- the proof. Its type spells out `List.Mem`: `∈` there would make the type
-- mention the instance itself.
instance List.decMem [auto eq: DecEq a] (x: a): (xs: List a) → Decidable (List.Mem x xs)
  | Nil => No (none => none)
  | Cons y ys => Decidable.or (eq.decide y x) (List.decMem x ys)

test "List.decMem" := 2 ∈ [1, 2, 3] ∧ 4 ∉ [1, 2, 3] ∧ 'a' ∉ []

test "List.decMem on a variable" := List.all [3, 1] (x => x ∈ [1, 2, 3])

-- No element of the first list is in the second.
def List.Disjoint (xs: List a) (ys: List a): Prop := List.All (x => x ∉ ys) xs

-- No element occurs twice.
def List.Distinct: List a → Prop
  | Nil => Unit
  | Cons x xs => And (x ∉ xs) (List.Distinct xs)

theorem List.distinctNil: List.Distinct (Nil: List a) := Trivial

theorem List.distinctCons (x: a) (xs: List a) (h: x ∉ xs) (d: List.Distinct xs): List.Distinct (Cons x xs) := Both h d

-- An element of two lists joined is in one of them.
theorem List.memAppend (x: a): (xs: List a) → (ys: List a) → x ∈ List.append xs ys → Or (x ∈ xs) (x ∈ ys)
  | Nil, ys, h => Inr h
  | Cons z zs, ys, Inl h => Inl (Inl h)
  | Cons z zs, ys, Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- And back: an element of either list is in the two joined.
theorem List.memAppendLeft (x: a): (xs: List a) → (ys: List a) → x ∈ xs → x ∈ List.append xs ys
  | Nil, ys, m => Void.exfalso m
  | Cons z zs, ys, Inl e => Inl e
  | Cons z zs, ys, Inr m => Inr (List.memAppendLeft x zs ys m)

theorem List.memAppendRight (x: a): (xs: List a) → (ys: List a) → x ∈ ys → x ∈ List.append xs ys
  | Nil, ys, m => m
  | Cons z zs, ys, m => Inr (List.memAppendRight x zs ys m)

theorem List.memAppendExample: 3 ∈ List.append [1, 2] [3] := List.memAppendRight 3 [1, 2] [3] (Inl rfl)

-- `f x` is in `List.map xs f` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective (f: a → b) (inj: (x: a) → (y: a) → f x = f y → x = y) (x: a): (xs: List a) → f x ∈ List.map xs f → x ∈ xs
  | Nil, h => h
  | Cons z zs, Inl h => Inl (inj z x h)
  | Cons z zs, Inr h => Inr (List.memMapInjective f inj x zs h)

-- If `x` is in `xs`, `f x` is in `List.map xs f`.
theorem List.memMap: (xs: List a) → (x: a) → x ∈ xs → (f: a → b) → f x ∈ List.map xs f
  | Nil, x, h, f => h
  | Cons z zs, x, Inl h, f => Inl (Eq.cong f h)
  | Cons z zs, x, Inr h, f => Inr (List.memMap zs x h f)

-- Use "some element satisfies `p`": take that element, know it is in the
-- list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim (p: a → Prop) (goal: Prop): (xs: List a) → List.Any p xs → ((x: a) → x ∈ xs → p x → goal) → goal
  | Nil, h, k => Void.exfalso h
  | Cons z zs, Inl h, k => k z (Inl rfl) h
  | Cons z zs, Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

-- And to prove it: an element of the list that satisfies `p`. (For the
-- `Bool` `List.any`, `List.anyOfMem`.)
theorem List.anyIntro (p: a → Prop) (x: a): (xs: List a) → x ∈ xs → p x → List.Any p xs
  | Nil, m, px => Void.exfalso m
  | Cons z zs, Inl e, px => Inl (rewrite e in px)
  | Cons z zs, Inr m, px => Inr (List.anyIntro p x zs m px)

theorem List.anyIntroExample: List.Any (n => n > 2) [1, 2, 3] := List.anyIntro (n => n > 2) 3 [1, 2, 3] (Inr (Inr (Inl rfl))) rfl

-- What is in `List.map xs f` is `f x` for some `x` in `xs` (said with
-- `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny: (xs: List a) → (f: a → b) → (y: b) → y ∈ List.map xs f → List.Any (x => f x = y) xs
  | Nil, f, y, h => h
  | Cons z zs, f, y, Inl h => Inl h
  | Cons z zs, f, y, Inr h => Inr (List.memMapAny zs f y h)

-- What `(.filter p)` keeps was in the list, and passes `p`.
theorem List.memFilter: (xs: List a) → (p: a → Bool) → (x: a) → x ∈ List.filter xs p → And (x ∈ xs) (p x = True)
  | Nil, p, x, h => Void.exfalso h
  | Cons y ys, p, x, h =>
    match e: p y with
      | True =>
        match h with
          | Inl q => Both (Inl q) (rewrite q at e)
          | Inr m =>
            match List.memFilter ys p x m with
              | Both inYs px => Both (Inr inYs) px
      | False =>
        match List.memFilter ys p x h with
          | Both inYs px => Both (Inr inYs) px

-- A `filter` that keeps nothing of the list is empty.
theorem List.filterNone (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = False) → List.filter xs p = Nil
  | Nil, h => rfl
  | Cons x xs, h => rewrite h x (Inl rfl) in List.filterNone p xs (y m => h y (Inr m))

-- A `filter` that keeps all of the list is the list.
theorem List.filterAll (p: a → Bool): (xs: List a) → ((x: a) → x ∈ xs → p x = True) → List.filter xs p = xs
  | Nil, h => rfl
  | Cons x xs, h => rewrite h x (Inl rfl) in Eq.cong (Cons x) (List.filterAll p xs (y m => h y (Inr m)))

-- No successor is zero, and every one is at least 1.
theorem List.filterNoneExample (xs: List Nat): List.filter (List.map xs Succ) (n => n == 0) = Nil :=
  List.filterNone (n => n == 0) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) ((n == 0) = False) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

theorem List.filterAllExample (xs: List Nat): List.filter (List.map xs Succ) (n => Nat.leq 1 n) = List.map xs Succ :=
  List.filterAll (n => Nat.leq 1 n) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) (Nat.leq 1 n = True) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e in rfl))

-- The run `List.rangeFrom c s` holds the numbers from `s` up to, not
-- including, `s + c`.
theorem List.memRangeFrom (x: Nat): (c: Nat) → (s: Nat) → x ∈ List.rangeFrom c s → And (s ≤ x) (x < s + c)
  | Zero, s, h => Void.exfalso h
  | Succ c, s, Inl q => rewrite <- q in Both (Nat.leRefl s) (Nat.ltAddSuccSelf s c)
  | Succ c, s, Inr m =>
    match List.memRangeFrom x c (Succ s) m with
      | Both lo hi => Both (Nat.lessLe s x lo) (Nat.ltAddSucc s c x hi)

-- `List.between lo hi` holds the numbers from `lo` to `hi`, both included.
-- The numbers are implicit, for use on a `List.Member`'s `isIn`.
theorem List.memBetween [x lo hi: Nat] (h: x ∈ List.between lo hi): And (lo ≤ x) (x ≤ hi) :=
  match List.memRangeFrom x (hi + 1 - lo) lo h with
    | Both above below => Both above (Nat.ltCongRight x (hi + 1) (Succ hi) (Nat.addOne hi) (Nat.ltOfRunSub lo x (hi + 1) above below))

-- The other way: every number from `s` up to, not including, `s + c` is in
-- the run `List.rangeFrom c s`.
theorem List.memRangeFromIntro (x: Nat): (c: Nat) → (s: Nat) → s ≤ x → x < s + c → x ∈ List.rangeFrom c s
  | Zero, s, lo, hi => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) s x (Nat.ltCongRight x (s + 0) s (Nat.addZero s) hi) lo))
  | Succ c, s, lo, hi =>
    match e: Nat.leq (Succ s) x with
      | True => Inr (List.memRangeFromIntro x c (Succ s) e (Nat.ltSuccAdd s c x hi))
      | False => Inl (Nat.leAntisym s x lo (Nat.leqFalse (Succ s) x e))

-- And for `List.between lo hi`: every number from `lo` to `hi`, both included.
theorem List.memBetweenIntro (x: Nat) (lo: Nat) (hi: Nat) (above: lo ≤ x) (below: x ≤ hi): x ∈ List.between lo hi :=
  List.memRangeFromIntro x (hi + 1 - lo) lo above
    (Nat.ltCongRight x (hi + 1) (lo + (hi + 1 - lo))
      (Eq.sym (Nat.addSubCancel lo (hi + 1) (Nat.leTrans lo x (hi + 1) above (Nat.leTrans x hi (hi + 1) below (Nat.leCongRight hi (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leSucc hi))))))
      (Nat.ltCongRight x (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leLessSucc x hi below)))

-- A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro (f: a → List b) (x: a) (y: b): (xs: List a) → x ∈ xs → y ∈ f x → y ∈ List.flatMap xs f
  | Nil, h, m => Void.exfalso h
  | Cons z zs, Inl h, m => List.anyAppendLeft (w => w = y) (f z) (List.concat (List.map zs f)) (rewrite h in m)
  | Cons z zs, Inr h, m => List.anyAppendRight (w => w = y) (f z) (List.concat (List.map zs f)) (List.memFlatMapIntro f x y zs h m)

-- And back: what is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim (f: a → List b) (y: b): (xs: List a) → y ∈ List.flatMap xs f → List.Any (x => y ∈ f x) xs
  | Nil, h => h
  | Cons z zs, h =>
    match List.memAppend y (f z) (List.concat (List.map zs f)) h with
      | Inl m => Inl m
      | Inr m => Inr (List.memFlatMapElim f y zs m)

-- Mapping an injective function keeps a list distinct.
theorem List.distinctMap: (xs: List a) → List.Distinct xs → (f: a → b) → (inj: (x: a) → (y: a) → f x = f y → x = y) → List.Distinct (List.map xs f)
  | Nil, d, f, inj => Trivial
  | Cons x xs, Both h d, f, inj => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap xs d f inj)

-- Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend: (xs: List a) → (ys: List a) → List.Distinct xs → List.Distinct ys → List.Disjoint xs ys → List.Distinct (List.append xs ys)
  | Nil, ys, dx, dy, dj => dy
  | Cons x xs, ys, Both hx dx, dy, Both hj dj =>
    Both
      (m => match List.memAppend x xs ys m with
        | Inl inXs => hx inXs
        | Inr inYs => hj inYs)
      (List.distinctAppend xs ys dx dy dj)

-- The same head in front of two lists gives the same list only if the tails
-- were the same.
theorem List.consInjective (x: a) (ys: List a) (zs: List a) (p: Cons x ys = Cons x zs): ys = zs := Eq.cong (.drop 1) p

-- A list starting with x isn't among lists that all start with y, a
-- different element.
theorem List.notMemMapCons (x: a) (y: a) (ne: Not (x = y)) (xs: List a): (ys: List (List a)) → Cons x xs ∉ List.map ys (Cons y)
  | Nil, m => m
  | Cons z zs, Inl p => ne (Eq.sym (Eq.cong (.headOr x) p))
  | Cons z zs, Inr q => List.notMemMapCons x y ne xs zs q

-- Lists that all start with x and lists that all start with a different y
-- have none in common.
theorem List.disjointMapCons (ys: List (List a)) (x: a) (y: a) (ne: Not (x = y)): (xs: List (List a)) →
    List.Disjoint (List.map xs (Cons x)) (List.map ys (Cons y))
  | Nil => Trivial
  | Cons z zs => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons ys x y ne zs)

-- A run of numbers has no repeats.
theorem List.distinctRangeFrom: (c: Nat) → (s: Nat) → List.Distinct (List.rangeFrom c s)
  | Zero, s => Trivial
  | Succ c, s =>
    Both (m => match List.memRangeFrom s c (Succ s) m with
        | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

theorem List.distinctBetween (lo: Nat) (hi: Nat): List.Distinct (List.between lo hi) := List.distinctRangeFrom (hi + 1 - lo) lo

-- Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem (p: a → Prop): (xs: List a) → ((x: a) → x ∈ xs → p x) → List.All p xs
  | Nil, h => Trivial
  | Cons z zs, h => Both (h z (Inl rfl)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

-- A `flatMap` of distinct lists has no repeats if the list mapped over has none
-- and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap (f: a → List b) (key: b → a): (xs: List a) → List.Distinct xs →
    ((x: a) → x ∈ xs → List.Distinct (f x)) →
    ((x: a) → x ∈ xs → (y: b) → y ∈ f x → key y = x) →
    List.Distinct (List.flatMap xs f)
  | Nil, d, distinctEach, keyed => Trivial
  | Cons x xs, Both notLater later, distinctEach, keyed =>
    List.distinctAppend (f x) (List.flatMap xs f)
      (distinctEach x (Inl rfl))
      (List.distinctFlatMap f key xs later (z inXs => distinctEach z (Inr inXs)) (z inXs => keyed z (Inr inXs)))
      -- Nothing in `f x` is in a later `f z`: it would have key `x` and key `z`.
      (List.allOfMem (y => y ∉ List.flatMap xs f) (f x) (y fromX inLater =>
        List.anyElim (z => y ∈ f z) Void xs (List.memFlatMapElim f y xs inLater)
          (z inXs fromZ =>
            notLater (rewrite Eq.trans (Eq.sym (keyed x (Inl rfl) y fromX)) (keyed z (Inr inXs) y fromZ) in inXs))))

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v)
    (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map [1, 2] Succ) :=
  List.distinctMap [1, 2] List.distinctExample Succ (x y p => Nat.succInjective x y p)

theorem List.consInjectiveExample (ys: List Nat) (zs: List Nat) (p: Cons 1 ys = Cons 1 zs): ys = zs := List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map [[1], [2]] (Cons 0)) (List.map [[1], Nil] (Cons 1)) :=
  List.disjointMapCons [[1], Nil] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map [Nil] (Cons 0)) (List.map [Nil] (Cons 1))) :=
  List.distinctAppend (List.map [Nil] (Cons 0)) (List.map [Nil] (Cons 1))
    (List.distinctMap [Nil] (Both (m => m) Trivial) (Cons 0) (List.consInjective 0))
    (List.distinctMap [Nil] (Both (m => m) Trivial) (Cons 1) (List.consInjective 1))
    (List.disjointMapCons [Nil] 0 1 (p => Nat.succNotZero 0 (Eq.sym p)) [Nil])

theorem List.memBetweenIntroExample: 3 ∈ List.between 1 5 := List.memBetweenIntro 3 1 5 rfl rfl

theorem List.memFlatMapExample: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10]) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl rfl)) (Inr (Inl rfl))

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend [1] [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both (m => match m with
      | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
      | Inr v => v) Trivial)

-- What `List.All` says of an element of the list.
theorem List.allMem (p: a → Prop) (x: a): (xs: List a) → List.All p xs → x ∈ xs → p x
  | Nil, h, m => Void.exfalso m
  | Cons z zs, Both pz h, Inl e => rewrite <- e in pz
  | Cons z zs, Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

-- What `List.find` finds passes the test and is in the list.
theorem List.findSome: (xs: List a) → (p: a → Bool) → (y: a) → List.find xs p = Some y → And (p y = True) (y ∈ xs)
  | Nil, p, y, h => Void.exfalso (Option.noneNotSome y h)
  | Cons x xs, p, y, h =>
    match e: p x with
      | True => Both (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective x y h))) e) (Inl (Option.someInjective x y h))
      | False =>
        match List.findSome xs p y h with
          | Both py m => Both py (Inr m)

-- `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem: (xs: List a) → (p: a → Bool) → (x: a) → (px: p x = True) → x ∈ xs → List.find xs p = None → Void
  | Nil, p, x, px, m, h => m
  | Cons z zs, p, x, px, Inl e, h => Option.someNotNone x (rewrite e, px at h)
  | Cons z zs, p, x, px, Inr m, h =>
    match c: p z with
      | True => Option.someNotNone z h
      | False => List.findNoneNotMem zs p x px m h

-- An element that passes makes `List.any` true.
theorem List.anyOfMem: (xs: List a) → (q: a → Bool) → (y: a) → (qy: q y = True) → y ∈ xs → List.any xs q = True
  | Nil, q, y, qy, m => Void.exfalso m
  | Cons x xs, q, y, qy, Inl e => rewrite e, qy in rfl
  | Cons x xs, q, y, qy, Inr m =>
    match c: q x with
      | True => rfl
      | False => List.anyOfMem xs q y qy m

-- And back: when `List.any` is true, some element of the list passes.
theorem List.anyTrueElim: (xs: List a) → (p: a → Bool) → (goal: Prop) → List.any xs p = True → ((x: a) → x ∈ xs → p x = True → goal) → goal
  | Nil, p, goal, h, k => Void.exfalso (Bool.falseNotTrue h)
  | Cons z zs, p, goal, h, k =>
    match c: p z with
      | True => k z (Inl rfl) c
      | False => List.anyTrueElim zs p goal h (x inZs px => k x (Inr inZs) px)

-- What `(.find p)` finds passes any other test some element passes.
theorem List.findAny (xs: List a) (p: a → Bool) (q: a → Bool) (y: a) (qy: q y = True) (h: List.find xs p = Some y): List.any xs q = True :=
  match List.findSome xs p y h with
    | Both py m => List.anyOfMem xs q y qy m

-- With distinct keys, finding by an element's key finds that element (and
-- `List.findKey`, std/List/Sort.sw, says what is found has the key).
theorem List.findKeyDistinct [auto eq: DecEq k] (key: a → k): (xs: List a) → List.Distinct (List.map xs key) → (x: a) → x ∈ xs →
    List.find xs (y => key y == key x) = Some x
  | Nil, d, x, m => Void.exfalso m
  | Cons z zs, Both notMem d, x, Inl e => rewrite e, DecEq.refl (key x) in rfl
  | Cons z zs, Both notMem d, x, Inr m =>
    match c: key z == key x with
      | True => Void.exfalso (notMem (rewrite DecEq.sound (key z) (key x) c in List.memMap zs x m key))
      | False => List.findKeyDistinct key zs d x m

theorem List.findKeyDistinctExample: List.find [(1, "a"), (2, "b")] (y => y.fst == 2) = Some (2, "b") :=
  List.findKeyDistinct Pair.fst [(1, "a"), (2, "b")]
    (Both (m => match m with
        | Inl p => Nat.succNotZero 0 (Nat.succInjective 1 0 p)
        | Inr v => v)
      (Both (m => m) Trivial))
    (2, "b") (Inr (Inl rfl))

-- A key of part of the list is a key of the list.
theorem List.memMapOfSub (key: a → k) (s: List a) (xs: List a) (sub: (y: a) → y ∈ s → y ∈ xs) (z: k)
    (m: z ∈ List.map s key): z ∈ List.map xs key :=
  List.anyElim (y => key y = z) (z ∈ List.map xs key) s (List.memMapAny s key z m)
    (y inS e => rewrite <- e in List.memMap xs y (sub y inS) key)

-- Keeping some elements keeps their keys distinct.
theorem List.distinctMapFilter: (xs: List a) → (key: a → k) → (p: a → Bool) → List.Distinct (List.map xs key) →
    List.Distinct (List.map (List.filter xs p) key)
  | Nil, key, p, d => Trivial
  | Cons x xs, key, p, Both notMem d =>
    match e: p x with
      | True =>
        Both
          (m => notMem (List.memMapOfSub key (List.filter xs p) xs (y inFiltered => match List.memFilter xs p y inFiltered with
            | Both inXs py => inXs) (key x) m))
          (List.distinctMapFilter xs key p d)
      | False => List.distinctMapFilter xs key p d

-- Keeping some elements keeps them distinct.
theorem List.distinctFilter: (xs: List a) → (p: a → Bool) → List.Distinct xs → List.Distinct (List.filter xs p)
  | Nil, p, d => Trivial
  | Cons x xs, p, Both notMem d =>
    match e: p x with
      | True => Both (m => notMem (And.left (List.memFilter xs p x m))) (List.distinctFilter xs p d)
      | False => List.distinctFilter xs p d

-- A key of a `filterMap`'s result is the key of an element it came from,
-- when each result has the key of its element.
theorem List.memMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x) (z: k):
    (xs: List a) → z ∈ List.map (List.filterMap xs f) kb → z ∈ List.map xs ka
  | Nil, m => m
  | Cons x xs, m =>
    match e: f x with
      | None => Inr (List.memMapFilterMap f ka kb hk z xs m)
      | Some y =>
        match m with
          | Inl q => Inl (Eq.trans (Eq.sym (hk x y e)) q)
          | Inr r => Inr (List.memMapFilterMap f ka kb hk z xs r)

-- So `filterMap` keeps keys distinct.
theorem List.distinctMapFilterMap (f: a → Option b) (ka: a → k) (kb: b → k) (hk: (x: a) → (y: b) → f x = Some y → kb y = ka x):
    (xs: List a) → List.Distinct (List.map xs ka) → List.Distinct (List.map (List.filterMap xs f) kb)
  | Nil, d => Trivial
  | Cons x xs, Both notMem d =>
    match e: f x with
      | None => List.distinctMapFilterMap f ka kb hk xs d
      | Some y =>
        Both (m => notMem (rewrite <- hk x y e in List.memMapFilterMap f ka kb hk (kb y) xs m))
          (List.distinctMapFilterMap f ka kb hk xs d)

-- Two lists with distinct keys and no key in common, joined, have distinct keys.
theorem List.distinctMapAppend (key: a → k) (xs: List a) (ys: List a) (dx: List.Distinct (List.map xs key)) (dy: List.Distinct (List.map ys key))
    (dj: List.Disjoint (List.map xs key) (List.map ys key)): List.Distinct (List.map (List.append xs ys) key) :=
  rewrite List.mapAppend xs ys key in List.distinctAppend (List.map xs key) (List.map ys key) dx dy dj

theorem List.distinctMapFilterExample: List.Distinct (List.map (List.filter [1, 2] (x => Nat.leq 2 x)) Succ) :=
  List.distinctMapFilter [1, 2] Succ (x => Nat.leq 2 x) List.distinctMapExample

-- Mapping with a state threaded left to right (Haskell's `mapAccumL`).
-- `xs` is the main value: `xs.mapAccumLeft 0 (s x => MkPair (s + x) (s * x))`.
-- The function takes the state and an element and gives the next state and
-- the mapped element; the result is the final state and the mapped list.
-- A loop: `done` holds the mapped elements so far, newest first.
@[noReceiver]
def List.mapAccumLeftGo (f: s → a → Pair s b) (state: s) (done: List b): List a → Pair s (List b)
  | Nil => MkPair state (List.reverseOnto done Nil)
  | Cons x xs =>
    let next := f state x
    List.mapAccumLeftGo f (Pair.fst next) (Cons (Pair.snd next) done) xs

def List.mapAccumLeft (xs: List a) (initial: s) (f: s → a → Pair s b): Pair s (List b) := List.mapAccumLeftGo f initial Nil xs

-- Splits a list of pairs into the list of firsts and the list of seconds.
def List.unzip (ps: List (Pair a b)): Pair (List a) (List b) := MkPair (List.map ps Pair.fst) (List.map ps Pair.snd)

-- Dropping elements never makes a list longer.
theorem List.lengthDropLe: (xs: List a) → (n: Nat) → List.length (List.drop xs n) ≤ List.length xs
  | xs, Zero => Nat.leRefl (List.length xs)
  | Nil, Succ n => rfl
  | Cons x xs, Succ n => Nat.leTrans (List.length (List.drop xs n)) (List.length xs) (Succ (List.length xs)) (List.lengthDropLe xs n) (Nat.leSucc (List.length xs))

-- Dropping at least one element of a non-empty list leaves a shorter list.
theorem List.dropConsLess: (xs: List a) → (n: Nat) → (x: a) → n ≠ 0 → List.length (List.drop (Cons x xs) n) < List.length (Cons x xs)
  | xs, Zero, x, h => Void.exfalso (h rfl)
  | xs, Succ n, x, h => Nat.leLessSucc (List.length (List.drop xs n)) (List.length xs) (List.lengthDropLe xs n)

-- Chunks of `n` elements, in order; the last chunk is shorter when `n` doesn't
-- divide the length. `n = 0` is no sensible chunk size, so it gives the whole
-- list as one chunk (`[xs]`, or `[]` for an empty `xs`).
@[noReceiver]
def List.chunksOfPositive (n: Nat) (xs: List a) [auto pos: n ≠ 0]: List (List a)
    decreasing List.length xs
:=
  match xs with
    | Nil => Nil
    | Cons y ys => Cons (List.take (Cons y ys) n) (List.chunksOfPositive n (List.drop (Cons y ys) n) [decreasing := List.dropConsLess ys n y pos])

-- `xs` is the main value: `xs.chunksOf 2`. `[1, 2, 3].chunksOf 2` is
-- `[[1, 2], [3]]`.
def List.chunksOf (xs: List a) (n: Nat): List (List a) :=
  match n with
    | Zero => match xs with
      | Nil => Nil
      | Cons y ys => Cons (Cons y ys) Nil
    | Succ k => List.chunksOfPositive (Succ k) xs

-- The elements without repeats, keeping the first occurrence of each and the
-- order. `seen` is what came before. Needs only `DecEq`, so it is quadratic:
-- each element is compared with every one kept before it.
@[noReceiver]
def List.distinctFrom [auto eq: DecEq a] (seen: List a): List a → List a
  | Nil => Nil
  | Cons x xs => if List.any seen (== x) then List.distinctFrom seen xs else Cons x (List.distinctFrom (Cons x seen) xs)

-- `List.distinct` for a type with `==` but no ordering: the same result,
-- quadratic. `[3, 1, 3, 2, 1].distinctEq` is `[3, 1, 2]`. With an ordering,
-- use `List.distinct` (std/List/Distinct.sw, with the theorems about both),
-- O(n log n).
def List.distinctEq [auto eq: DecEq a] (xs: List a): List a := List.distinctFrom Nil xs

test "List.mapAccumLeft" := [1, 2, 3].mapAccumLeft 0 (s x => MkPair (s + x) (s * x)) == MkPair 6 [0, 2, 9]
test "List.mapAccumLeft empty" := (Nil: List Nat).mapAccumLeft 7 (s x => MkPair (s + x) x) == MkPair 7 Nil
test "List.unzip" := List.unzip [MkPair 1 True, MkPair 2 False] == MkPair [1, 2] [True, False]
test "List.unzip empty" := List.unzip (Nil: List (Pair Nat Nat)) == MkPair Nil Nil
test "List.chunksOf" := List.chunksOf [1, 2, 3, 4, 5] 2 == [[1, 2], [3, 4], [5]]
test "List.chunksOf exact" := List.chunksOf [1, 2, 3, 4] 2 == [[1, 2], [3, 4]]
test "List.chunksOf bigger than the list" := List.chunksOf [1, 2] 5 == [[1, 2]]
test "List.chunksOf empty" := List.chunksOf (Nil: List Nat) 3 == Nil
test "List.chunksOf zero is one chunk" := List.chunksOf [1, 2, 3] 0 == [[1, 2, 3]] ∧ List.chunksOf (Nil: List Nat) 0 == Nil
test "List.distinctEq" := [3, 1, 3, 2, 1].distinctEq == [3, 1, 2]
test "List.distinctEq empty" := (Nil: List Nat).distinctEq == Nil
test "List.distinctEq all repeats" := [4, 4, 4].distinctEq == [4]
test "List.distinctEq already distinct" := [2, 5, 1].distinctEq == [2, 5, 1]
-- Second batch (SW-235). The main value comes first, the function last.

-- The element with the largest key, or `None` for an empty list. When several
-- keys are largest, the FIRST of those elements wins: `[(1, "a"), (3, "b"),
-- (3, "c")].maxBy Pair.fst` is `Some (3, "b")`. (Haskell's `maximumBy` and
-- Clojure's `max-key` return the last one, so a port must not assume they agree.)
def List.maxByStep [auto ord: Ord b] (f: a → b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Less => x
  | _ => best

def List.maxBy [auto ord: Ord b] (xs: List a) (f: a → b): Option a :=
  match xs with
    | Nil => None
    | Cons x ys => Some (List.foldLeft ys x (best y => List.maxByStep f best y))

-- The element with the smallest key; on a tie the FIRST one wins, as for
-- `List.maxBy`.
def List.minByStep [auto ord: Ord b] (f: a → b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Greater => x
  | _ => best

def List.minBy [auto ord: Ord b] (xs: List a) (f: a → b): Option a :=
  match xs with
    | Nil => None
    | Cons x ys => Some (List.foldLeft ys x (best y => List.minByStep f best y))

-- The longest prefix of elements satisfying `p`. `p` may perform abilities:
-- it runs in list order and isn't called after the first element that fails
-- it.
def List.takeWhile (xs: List a) (p: a → {e} Bool): {e} List a :=
  match xs with
    | Nil => Nil
    | Cons x ys => if p x then Cons x (List.takeWhile ys p) else Nil

-- What is left after `List.takeWhile`: from the first element not satisfying `p`.
def List.dropWhile (xs: List a) (p: a → Bool): List a :=
  match xs with
    | Nil => Nil
    | Cons x ys => if p x then List.dropWhile ys p else Cons x ys

-- `List.span`'s loop: `taken` is the prefix so far, reversed.
@[noReceiver]
def List.spanOnto (taken: List a) (p: a → {e} Bool): List a → {e} Pair (List a) (List a)
  | Nil => MkPair (List.reverse taken) Nil
  | Cons x xs => if p x then List.spanOnto (Cons x taken) p xs else MkPair (List.reverse taken) (Cons x xs)

-- `List.takeWhile` and `List.dropWhile` together (`List.spanTakeDrop`), in
-- one pass. `p` may perform abilities: it runs in list order and isn't
-- called after the first element that fails it.
def List.span (xs: List a) (p: a → {e} Bool): {e} Pair (List a) (List a) := List.spanOnto Nil p xs

-- The first `n` elements and the rest: `xs.splitAt 2` is `(xs.take 2, xs.drop 2)`.
def List.splitAt (xs: List a) (n: Nat): Pair (List a) (List a) := MkPair (List.take xs n) (List.drop xs n)

-- Without the last `n` elements (all of them if there are fewer).
def List.dropRight (xs: List a) (n: Nat): List a := List.take xs (List.length xs - n)

-- Every suffix, longest first, ending with the empty list:
-- `[1, 2].tails` is `[[1, 2], [2], []]`.
def List.tails: List a → List (List a)
  | Nil => Cons Nil Nil
  | Cons x xs => Cons (Cons x xs) (List.tails xs)

-- The index of the first element satisfying `p`.
@[noReceiver]
def List.findIndexFrom (i: Nat) (p: a → Bool): List a → Option Nat
  | Nil => None
  | Cons x xs => if p x then Some i else List.findIndexFrom (Succ i) p xs

def List.findIndex (xs: List a) (p: a → Bool): Option Nat := List.findIndexFrom 0 p xs

-- Each element with its index from `i`.
@[noReceiver]
def List.withIndexFrom (i: Nat): List a → List (Pair Nat a)
  | Nil => Nil
  | Cons x xs => Cons (MkPair i x) (List.withIndexFrom (Succ i) xs)

-- Pairs each element with its position, counting from 0, the position first
-- (Rust's `enumerate`): `["a", "b"].withIndex` is `[(0, "a"), (1, "b")]`.
def List.withIndex (xs: List a): List (Pair Nat a) := List.withIndexFrom 0 xs

-- One step of `List.findMap`: the `Some` found, or else the search of the
-- rest, which runs only then. The rest is a function of no arguments so that
-- an effectful `f` isn't called after the first `Some`; a function of its
-- own (not a `match` in `findMap`) so the backends inline it and
-- `findMap` stays a loop.
@[noReceiver]
def List.findMapStep: Option b → (rest: () → {e} Option b) → {e} Option b
  | Some y, rest => Some y
  | None, rest => rest ()

-- The first `Some` that `f` gives (Lean's `findSome?`, Scala's `collectFirst`).
-- `f` may perform abilities: it runs in list order and isn't called after
-- the first `Some`.
def List.findMap (xs: List a) (f: a → {e} Option b): {e} Option b :=
  match xs with
    | Nil => None
    | Cons x ys => List.findMapStep (f x) (() => List.findMap ys f)

-- `findMap` is the first of the `filterMap` results, found without building
-- the rest.
theorem List.findMapIsHeadFilterMap: (xs: List a) → (f: a → Option b) → List.findMap xs f = List.head (List.filterMap xs f)
  | Nil, f => rfl
  | Cons x xs, f =>
    match f x with
      | None => List.findMapIsHeadFilterMap xs f
      | Some y => rfl

-- Maps, then joins: `xs.flatMap f` is `List.concat (List.map xs f)`. `f` may
-- perform abilities, which run in list order.
def List.flatMap (xs: List a) (f: a → {e} List b): {e} List b := List.concat (List.map xs f)

-- Every pair, the first elements in order and the second elements within
-- each: `[1, 2].cross ["a", "b"]` is `[(1, "a"), (1, "b"), (2, "a"), (2, "b")]`.
def List.cross (xs: List a) (ys: List b): List (Pair a b) := List.flatMap xs (x => List.map ys (y => MkPair x y))

-- Every element with each later one, in order: `[1, 2, 3].pairs` is
-- `[(1, 2), (1, 3), (2, 3)]`. A list of n elements has n(n - 1)/2 of them.
def List.pairs: List a → List (Pair a a)
  | Nil => Nil
  | Cons x xs => List.append (List.map xs (y => MkPair x y)) (List.pairs xs)

theorem List.lengthTails: (xs: List a) → List.length (List.tails xs) = Succ (List.length xs)
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (List.lengthTails xs)

theorem List.splitAtFst (xs: List a) (n: Nat): Pair.fst (List.splitAt xs n) = List.take xs n := rfl

-- The loop's prefix is `takeWhile`'s, after what it had taken.
theorem List.spanOntoTakeDrop (p: a → Bool): (taken: List a) → (xs: List a) →
    List.spanOnto taken p xs = MkPair (List.reverseOnto taken (List.takeWhile xs p)) (List.dropWhile xs p)
  | taken, Nil => rfl
  | taken, Cons x xs =>
    match p x with
      | True => List.spanOntoTakeDrop p (Cons x taken) xs
      | False => rfl

-- `span` is `takeWhile` and `dropWhile` (its definition before it became one
-- pass).
theorem List.spanTakeDrop (xs: List a) (p: a → Bool): List.span xs p = MkPair (List.takeWhile xs p) (List.dropWhile xs p) :=
  List.spanOntoTakeDrop p Nil xs

theorem List.spanExample: List.span [1, 2, 3, 1] (x => Nat.leq x 2) = MkPair [1, 2] [3, 1] := rfl

test "List.maxBy" := [MkPair 2 "bb", MkPair 1 "a", MkPair 3 "ccc"].maxBy Pair.fst == Some (MkPair 3 "ccc") ∧ (Nil: List Nat).maxBy (x => x) == None
test "List.maxBy first wins a tie" := [MkPair 1 "a", MkPair 3 "b", MkPair 3 "c"].maxBy Pair.fst == Some (MkPair 3 "b")
test "List.minBy first wins a tie" := [MkPair 3 "z", MkPair 1 "a", MkPair 1 "b"].minBy Pair.fst == Some (MkPair 1 "a") ∧ (Nil: List Nat).minBy (x => x) == None
test "List.takeWhile and dropWhile" := [1, 2, 5, 1].takeWhile (x => Nat.leq x 2) == [1, 2] ∧ [1, 2, 5, 1].dropWhile (x => Nat.leq x 2) == [5, 1]
test "List.takeWhile all and none" := [1, 2].takeWhile (x => Nat.leq x 8) == [1, 2] ∧ [1, 2].dropWhile (x => Nat.leq x 8) == Nil ∧ [4].takeWhile (x => Nat.leq x 2) == Nil
test "List.span" := List.span [1, 2, 5, 1] (x => Nat.leq x 2) == MkPair [1, 2] [5, 1] ∧ List.span (Nil: List Nat) (x => Nat.leq x 2) == MkPair Nil Nil
test "List.span dot" := [1, 2, 5, 1].span (x => Nat.leq x 2) == MkPair [1, 2] [5, 1]
test "List.splitAt" := [1, 2, 3].splitAt 1 == MkPair [1] [2, 3] ∧ [1, 2].splitAt 5 == MkPair [1, 2] Nil ∧ [1, 2].splitAt 0 == MkPair Nil [1, 2]
test "List.dropRight" := [1, 2, 3, 4].dropRight 1 == [1, 2, 3] ∧ [1, 2].dropRight 5 == Nil ∧ [1, 2].dropRight 0 == [1, 2]
test "List.tails" := [1, 2].tails == [[1, 2], [2], Nil] ∧ (Nil: List Nat).tails == [Nil]
test "List.findIndex" := [5, 6, 7].findIndex (x => Nat.leq 6 x) == Some 1 ∧ [5].findIndex (x => Nat.leq 10 x) == None
test "List.withIndex" := ["a", "b"].withIndex == [MkPair 0 "a", MkPair 1 "b"] ∧ (Nil: List Nat).withIndex == Nil
test "List.findMap" := [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == Some 30 ∧ [1].findMap (x => (None: Option Nat)) == None
test "List.findMap is the head of filterMap" :=
  [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == ([1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 10) else None)).head ∧
    [1].findMap (x => (None: Option Nat)) == ([1].filterMap (x => (None: Option Nat))).head
test "List.between" := List.between 2 5 == [2, 3, 4, 5] ∧ List.between 3 3 == [3] ∧ List.between 4 2 == Nil ∧ List.between 0 1 == [0, 1]
test "List.flatMap" := [1, 2, 3].flatMap (x => List.replicate x x) == [1, 2, 2, 3, 3, 3]
test "List.pairs" := [1, 2, 3].pairs == [MkPair 1 2, MkPair 1 3, MkPair 2 3] ∧ (Nil: List Nat).pairs == Nil ∧ [1].pairs == (Nil: List (Pair Nat Nat))
test "List.pairs count" := List.length (List.range 10).pairs == 45
test "List.cross" := [1, 2].cross ["a", "b"] == [MkPair 1 "a", MkPair 1 "b", MkPair 2 "a", MkPair 2 "b"] ∧ [1].cross (Nil: List Nat) == Nil

-- `map` through the other list functions (SW-198, day 8).

theorem List.mapAppend: (xs: List a) → (ys: List a) → (f: a → b) → List.map (List.append xs ys) f = List.append (List.map xs f) (List.map ys f)
  | Nil, ys, f => rfl
  | Cons x xs, ys, f => rewrite List.mapAppend xs ys f

theorem List.takeMap: (xs: List a) → (k: Nat) → (f: a → b) → List.take (List.map xs f) k = List.map (List.take xs k) f
  | xs, Zero, f => rfl
  | Nil, Succ k, f => rfl
  | Cons x xs, Succ k, f => rewrite List.takeMap xs k f

-- The first `k` of two lists combined are the first `k` of each combined.
theorem List.takeZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.take (List.zipWith xs ys f) k = List.zipWith (List.take xs k) (List.take ys k) f
  | xs, ys, Zero => rfl
  | Nil, ys, Succ k => rfl
  | Cons x xs, Nil, Succ k => rfl
  | Cons x xs, Cons y ys, Succ k => Eq.cong (Cons (f x y)) (List.takeZipWith f xs ys k)

theorem List.takeZipWithExample: List.take (List.zipWith [1, 2, 3] [10, 20, 30] Nat.add) 2 = List.zipWith [1, 2] [10, 20] Nat.add :=
  List.takeZipWith Nat.add [1, 2, 3] [10, 20, 30] 2

theorem List.foldLeftMap: (xs: List a) → (z: c) → (f: c → b → c) → (g: a → b) →
    List.foldLeft (List.map xs g) z f = List.foldLeft xs z (acc x => f acc (g x))
  | Nil, z, f, g => rfl
  | Cons x xs, z, f, g => List.foldLeftMap xs (f z (g x)) f g

theorem List.anyMap: (xs: List a) → (p: b → Bool) → (f: a → b) → List.any (List.map xs f) p = List.any xs (x => p (f x))
  | Nil, p, f => rfl
  | Cons x xs, p, f => rewrite List.anyMap xs p f

theorem List.countMap (xs: List a) (p: b → Bool) (f: a → b): List.count (List.map xs f) p = List.count xs (x => p (f x)) :=
  List.foldLeftMap xs 0 (n x => Nat.succIf n (p x)) f

theorem List.occurrencesMap: (xs: List a) → (f: a → b) → (p: b → Bool) → List.occurrences (List.map xs f) p = List.occurrences xs (x => p (f x))
  | Nil, f, p => rfl
  | Cons x xs, f, p => rewrite List.occurrencesMap xs f p in rfl

-- Mapping both lists of a permutation keeps it one.
theorem List.permMap (xs: List a) (ys: List a) (h: List.Perm xs ys) (f: a → b): List.Perm (List.map xs f) (List.map ys f) :=
  p => rewrite List.occurrencesMap xs f p, List.occurrencesMap ys f p in h (x => p (f x))

-- Counting what `(.filter keep)` kept is counting what passes both tests.
theorem List.occurrencesFilter: (xs: List a) → (keep: a → Bool) → (p: a → Bool) →
    List.occurrences (List.filter xs keep) p = List.occurrences xs (x => p x ∧ keep x)
  | Nil, keep, p => rfl
  | Cons x xs, keep, p =>
    match e: keep x with
      | True =>
        rewrite List.occurrencesFilter xs keep p in
          match p x with
            | True => rfl
            | False => rfl
      | False =>
        rewrite List.occurrencesFilter xs keep p in
          match p x with
            | True => rfl
            | False => rfl

-- The first k numbers of a longer run.
theorem List.takeRangeFrom: (k: Nat) → (n: Nat) → (s: Nat) → k ≤ n → List.take (List.rangeFrom n s) k = List.rangeFrom k s
  | Zero, n, s, h => rfl
  | Succ k, Zero, s, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Succ n, s, h => rewrite List.takeRangeFrom k n (Succ s) h

-- The pairs of a mapped list are the list's pairs, mapped.
theorem List.pairsMap: (xs: List a) → (f: a → b) → List.pairs (List.map xs f) = List.map (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p)))
  | Nil, f => rfl
  | Cons x xs, f =>
    rewrite List.mapAppend (List.map xs (y => MkPair x y)) (List.pairs xs) (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))),
      List.mapMap xs (y => MkPair (f x) y) f, List.mapMap xs (p => MkPair (f (Pair.fst p)) (f (Pair.snd p))) (y => MkPair x y),
      List.pairsMap xs f

-- Callbacks that agree on the list's elements (not everywhere, as for
-- `List.mapCong`) give the same result.
theorem List.mapCongMem: (xs: List a) → (f1: a → b) → (f2: a → b) → ((x: a) → (m: x ∈ xs) → f1 x = f2 x) → List.map xs f1 = List.map xs f2
  | Nil, f1, f2, ef => rfl
  | Cons x xs, f1, f2, ef => rewrite ef x (Inl rfl), List.mapCongMem xs f1 f2 (y m => ef y (Inr m))

theorem List.filterCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.filter xs p1 = List.filter xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x (Inl rfl), List.filterCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.anyCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.any xs p1 = List.any xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x (Inl rfl), List.anyCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.occurrencesCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) →
    List.occurrences xs p1 = List.occurrences xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x (Inl rfl), List.occurrencesCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.foldLeftCongMem: (xs: List a) → (z: b) → (f1: b → a → b) → (f2: b → a → b) → ((acc: b) → (x: a) → (m: x ∈ xs) → f1 acc x = f2 acc x) →
    List.foldLeft xs z f1 = List.foldLeft xs z f2
  | Nil, z, f1, f2, ef => rfl
  | Cons x xs, z, f1, f2, ef =>
    Eq.trans (Eq.cong (t => List.foldLeft xs t f1) (ef z x (Inl rfl))) (List.foldLeftCongMem xs (f2 z x) f1 f2 (acc y m => ef acc y (Inr m)))

-- Over a run of numbers, the facts are the run's bounds. `rewrite` tries a
-- function's `…CongRange` lemma first, then `…CongMem`, then `…Cong`, and
-- rewriting inside the function has the facts as hypotheses.
theorem List.mapCongRange (f1: Nat → b) (f2: Nat → b) (c: Nat) (s: Nat)
    (ef: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → f1 x = f2 x):
    List.map (List.rangeFrom c s) f1 = List.map (List.rangeFrom c s) f2 :=
  List.mapCongMem (List.rangeFrom c s) f1 f2 (x m => ef x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.filterCongRange (p1: Nat → Bool) (p2: Nat → Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → p1 x = p2 x):
    List.filter (List.rangeFrom c s) p1 = List.filter (List.rangeFrom c s) p2 :=
  List.filterCongMem (List.rangeFrom c s) p1 p2 (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.anyCongRange (p1: Nat → Bool) (p2: Nat → Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → p1 x = p2 x):
    List.any (List.rangeFrom c s) p1 = List.any (List.rangeFrom c s) p2 :=
  List.anyCongMem (List.rangeFrom c s) p1 p2 (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.occurrencesCongRange (p1: Nat → Bool) (p2: Nat → Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → p1 x = p2 x):
    List.occurrences (List.rangeFrom c s) p1 = List.occurrences (List.rangeFrom c s) p2 :=
  List.occurrencesCongMem (List.rangeFrom c s) p1 p2 (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.foldLeftCongRange (f1: b → Nat → b) (f2: b → Nat → b) (z: b) (c: Nat) (s: Nat)
    (ef: (acc: b) → (x: Nat) → (low: s ≤ x) → (high: x < s + c) → f1 acc x = f2 acc x):
    List.foldLeft (List.rangeFrom c s) z f1 = List.foldLeft (List.rangeFrom c s) z f2 :=
  List.foldLeftCongMem (List.rangeFrom c s) z f1 f2
    (acc x m => ef acc x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

test "List.pairsMap" := (List.map [1, 2, 3] Succ).pairs == List.map [1, 2, 3].pairs (p => MkPair (Succ p.fst) (Succ p.snd))

-- the largest by folding Nat.max --------------------------------------------

-- The fold starts at `start` and never goes down.
theorem List.foldMaxGe: (xs: List Nat) → (start: Nat) → start ≤ List.foldLeft xs start Nat.max
  | Nil, start => Nat.leRefl start
  | Cons x xs, start => Nat.leTrans start (Nat.max start x) (List.foldLeft xs (Nat.max start x) Nat.max) (Nat.leMaxLeft start x) (List.foldMaxGe xs (Nat.max start x))

-- Every element is at most the largest.
theorem List.leFoldMax: (xs: List Nat) → (x: Nat) → (start: Nat) → x ∈ xs → x ≤ List.foldLeft xs start Nat.max
  | Nil, x, start, m => Void.exfalso m
  | Cons y ys, x, start, Inl e => rewrite <- e in Nat.leTrans y (Nat.max start y) (List.foldLeft ys (Nat.max start y) Nat.max) (Nat.leMaxRight start y) (List.foldMaxGe ys (Nat.max start y))
  | Cons y ys, x, start, Inr m => List.leFoldMax ys x (Nat.max start y) m

-- The largest is the start or one of the elements.
theorem List.foldMaxMem: (xs: List Nat) → (start: Nat) → Or (List.foldLeft xs start Nat.max = start) (List.foldLeft xs start Nat.max ∈ xs)
  | Nil, start => Inl rfl
  | Cons y ys, start =>
    match List.foldMaxMem ys (Nat.max start y) with
      | Inr m => Inr (Inr m)
      | Inl e =>
        match h: Nat.leq start y with
          | True => Inr (Inl (Eq.sym e))
          | False => Inl e

-- lengths, and sums over ranges ---------------------------------------------

-- Zipping two lists of at least n elements gives at least n.
theorem List.lengthZipWithAtLeast: (u: List a) → (n: Nat) → (v: List b) → n ≤ List.length u → n ≤ List.length v → (f: a → b → c) →
    n ≤ List.length (List.zipWith u v f)
  | u, Zero, v, hu, hv, f => rfl
  | Nil, Succ n, v, hu, hv, f => hu
  | Cons x xs, Succ n, Nil, hu, hv, f => hv
  | Cons x xs, Succ n, Cons y ys, hu, hv, f => List.lengthZipWithAtLeast xs n ys hu hv f

-- Running results: one more than the elements, the start first.
theorem List.lengthScanLeft: (xs: List a) → (start: b) → (f: b → a → b) → List.length (List.scanLeft xs start f) = Succ (List.length xs)
  | Nil, start, f => rfl
  | Cons x xs, start, f => Eq.cong Succ (List.lengthScanLeft xs (f start x) f)

-- A sum over the numbers below b is the sum below t and the sum from t up to b.
theorem List.sumByRangeSplit (f: Nat → Nat) (t: Nat) (b: Nat) (tb: t ≤ b):
    List.sumBy (List.rangeFrom b 0) f = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f :=
  calc List.sumBy (List.rangeFrom b 0) f
    _ = List.sumBy (List.rangeFrom (t + (b - t)) 0) f := Eq.cong (n => List.sumBy (List.rangeFrom n 0) f) (Eq.sym (Nat.addSubCancel t b tb))
    _ = List.sumBy (List.append (List.rangeFrom t 0) (List.rangeFrom (b - t) (0 + t))) f := Eq.cong (.sumBy f) (List.rangeFromAppend t (b - t) 0)
    _ = List.sumBy (List.rangeFrom t 0) f + List.sumBy (List.rangeFrom (b - t) t) f := List.sumByAppend (List.rangeFrom t 0) (List.rangeFrom (b - t) t) f

-- sums of zero -----------------------------------------------------------------

-- A sum of numbers is 0 only if each is.
theorem List.sumByZeroElim: (xs: List a) → (f: a → Nat) → List.sumBy xs f = 0 → (x: a) → x ∈ xs → f x = 0
  | Nil, f, h, x, m => Void.exfalso m
  | Cons y ys, f, h, x, Inl e => rewrite <- e in (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).left
  | Cons y ys, f, h, x, Inr m => List.sumByZeroElim ys f (Nat.addEqZero (f y) (List.sumBy ys f) (Eq.trans (Eq.sym (List.sumByCons ys y f)) h)).right x m

theorem List.sumByZeroIntro: (xs: List a) → (f: a → Nat) → ((x: a) → x ∈ xs → f x = 0) → List.sumBy xs f = 0
  | Nil, f, h => rfl
  | Cons y ys, f, h => rewrite List.sumByCons ys y f, h y (Inl rfl), List.sumByZeroIntro ys f (x m => h x (Inr m)) in rfl

-- filtering what can't pass anyway ------------------------------------------

-- Dropping elements that fail `q`, when only elements that pass `q` can pass
-- `p`, changes neither `any p` nor `count p`.
theorem List.anyFilter: (xs: List a) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) → List.any (List.filter xs q) p = List.any xs p
  | Nil, p, q, h => rfl
  | Cons x xs, p, q, h =>
    match e: q x with
      | True => rewrite List.anyFilter xs p q h in rfl
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.anyFilter xs p q h

theorem List.countFromFilter: (xs: List a) → (n: Nat) → (p: a → Bool) → (q: a → Bool) → (h: (x: a) → p x = True → q x = True) →
    List.foldLeft (List.filter xs q) n (k x => Nat.succIf k (p x)) = List.foldLeft xs n (k x => Nat.succIf k (p x))
  | Nil, n, p, q, h => rfl
  | Cons x xs, n, p, q, h =>
    match e: q x with
      | True => List.countFromFilter xs (Nat.succIf n (p x)) p q h
      | False =>
        match f: p x with
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (h x f)))
          | False => List.countFromFilter xs n p q h

theorem List.countFilter (xs: List a) (p: a → Bool) (q: a → Bool) (h: (x: a) → p x = True → q x = True): List.count (List.filter xs q) p = List.count xs p :=
  List.countFromFilter xs 0 p q h

-- membership through zip, take, drop and filter ------------------------------

-- Each pair of `List.zip xs ys` is an element of `xs` with one of `ys`.
theorem List.memZip (p: (a, b)): (xs: List a) → (ys: List b) → p ∈ List.zip xs ys → And (p.fst ∈ xs) (p.snd ∈ ys)
  | Nil, ys, m => Void.exfalso m
  | Cons x xs, Nil, m => Void.exfalso m
  | Cons x xs, Cons y ys, Inl e => rewrite <- e in Both (Inl rfl) (Inl rfl)
  | Cons x xs, Cons y ys, Inr m =>
    match List.memZip p xs ys m with
      | Both inXs inYs => Both (Inr inXs) (Inr inYs)

theorem List.memTake: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.take xs n → v ∈ xs
  | xs, v, Zero, m => Void.exfalso m
  | Nil, v, Succ n, m => m
  | Cons x xs, v, Succ n, Inl e => Inl e
  | Cons x xs, v, Succ n, Inr m => Inr (List.memTake xs v n m)

theorem List.memDrop: (xs: List a) → (v: a) → (n: Nat) → v ∈ List.drop xs n → v ∈ xs
  | xs, v, Zero, m => m
  | Nil, v, Succ n, m => m
  | Cons x xs, v, Succ n, m => Inr (List.memDrop xs v n m)

-- What passes the test is kept.
theorem List.memFilterIntro: (xs: List a) → (p: a → Bool) → (v: a) → v ∈ xs → p v = True → v ∈ List.filter xs p
  | Nil, p, v, m, h => m
  | Cons x xs, p, v, Inl e, h => rewrite <- e at h in (rewrite h in Inl e)
  | Cons x xs, p, v, Inr m, h =>
    match e: p x with
      | True => Inr (List.memFilterIntro xs p v m h)
      | False => List.memFilterIntro xs p v m h

-- Filtering a mapped list is mapping the filtered list.
theorem List.filterOfMap: (xs: List a) → (q: b → Bool) → (g: a → b) → List.filter (List.map xs g) q = List.map (List.filter xs (x => q (g x))) g
  | Nil, q, g => rfl
  | Cons x xs, q, g =>
    match e: q (g x) with
      | True => rewrite List.filterOfMap xs q g in rfl
      | False => List.filterOfMap xs q g

-- Each pair of `List.pairs xs` is two elements of `xs`.
theorem List.memPairs (p: (a, a)): (xs: List a) → p ∈ List.pairs xs → And (p.fst ∈ xs) (p.snd ∈ xs)
  | Nil, m => Void.exfalso m
  | Cons x xs, m =>
    match List.memAppend p (List.map xs (y => (x, y))) (List.pairs xs) m with
      | Inl first =>
        List.anyElim (y => (x, y) = p) (And (p.fst ∈ Cons x xs) (p.snd ∈ Cons x xs)) xs (List.memMapAny xs (y => (x, y)) p first)
          (y inXs e => rewrite <- e in Both (Inl rfl) (Inr inXs))
      | Inr later =>
        match List.memPairs p xs later with
          | Both one other => Both (Inr one) (Inr other)

-- The last element, if there is one, is an element.
theorem List.lastMem: (xs: List a) → (x: a) → List.last xs = Some x → x ∈ xs
  | Nil, x, h => Void.exfalso (Option.noneNotSome x h)
  | Cons y Nil, x, h => Inl (Option.someInjective y x h)
  | Cons y (Cons z zs), x, h => Inr (List.lastMem (Cons z zs) x h)

theorem List.lastMemExample: 3 ∈ [1, 2, 3] := List.lastMem [1, 2, 3] 3 rfl

-- `filterMap` keeps `y` when an element maps to `Some y` ...
theorem List.memFilterMapIntro (f: a → Option b) (x: a) (y: b): (xs: List a) → x ∈ xs → f x = Some y → y ∈ List.filterMap xs f
  | Nil, m, e => Void.exfalso m
  | Cons z zs, Inl q, e => rewrite q, e in Inl rfl
  | Cons z zs, Inr m, e =>
    match c: f z with
      | None => List.memFilterMapIntro f x y zs m e
      | Some w => Inr (List.memFilterMapIntro f x y zs m e)

-- ... and keeps nothing else.
theorem List.memFilterMapElim (f: a → Option b) (y: b): (xs: List a) → y ∈ List.filterMap xs f → List.Any (x => f x = Some y) xs
  | Nil, m => m
  | Cons z zs, m =>
    match c: f z with
      | None => Inr (List.memFilterMapElim f y zs m)
      | Some w =>
        match m with
          | Inl q => Inl (Eq.cong Some q)
          | Inr r => Inr (List.memFilterMapElim f y zs r)

-- Everything `filterMap` keeps has `q` when every element's `Some` result
-- would; and back.
theorem List.allFilterMap (q: b → Prop) (f: a → Option b): (xs: List a) → List.All (x => (y: b) → f x = Some y → q y) xs → List.All q (List.filterMap xs f)
  | Nil, h => Trivial
  | Cons z zs, Both hz h =>
    match c: f z with
      | None => List.allFilterMap q f zs h
      | Some w => Both (hz w rfl) (List.allFilterMap q f zs h)

theorem List.allFilterMapElim (q: b → Prop) (f: a → Option b): (xs: List a) → List.All q (List.filterMap xs f) → List.All (x => (y: b) → f x = Some y → q y) xs
  | Nil, h => Trivial
  | Cons z zs, h =>
    match c: f z with
      | None => Both (y e => Void.exfalso (Option.noneNotSome y e)) (List.allFilterMapElim q f zs h)
      | Some w =>
        match h with
          | Both hw rest => Both (y e => rewrite <- Option.someInjective w y e in hw) (List.allFilterMapElim q f zs rest)

theorem List.memFilterMapExample: 4 ∈ List.filterMap [1, 2, 3] (x => if x == 2 then Some (x * 2) else None) :=
  List.memFilterMapIntro (x => if x == 2 then Some (x * 2) else None) 2 4 [1, 2, 3] (Inr (Inl rfl)) rfl

-- `List.all` and `List.any` (the `Bool`s a program computes) are `List.All`
-- and `List.Any` (the propositions proofs use), so a lemma needs only one
-- form.
theorem List.allToAll (p: a → Bool): (xs: List a) → List.all xs p = True → List.All (x => p x = True) xs
  | Nil, h => Trivial
  | Cons x xs, h =>
    match c: p x with
      | True => Both rfl (List.allToAll p xs h)
      | False => Void.exfalso (Bool.falseNotTrue h)

theorem List.allOfAll (p: a → Bool): (xs: List a) → List.All (x => p x = True) xs → List.all xs p = True
  | Nil, h => rfl
  | Cons x xs, Both px h => rewrite px in List.allOfAll p xs h

theorem List.allIff (xs: List a) (p: a → Bool): List.all xs p = True ↔ List.All (x => p x = True) xs :=
  { forward = List.allToAll p xs, backward = List.allOfAll p xs }

theorem List.anyToAny (p: a → Bool): (xs: List a) → List.any xs p = True → List.Any (x => p x = True) xs
  | Nil, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, h =>
    match c: p x with
      | True => Inl rfl
      | False => Inr (List.anyToAny p xs h)

theorem List.anyOfAny (p: a → Bool): (xs: List a) → List.Any (x => p x = True) xs → List.any xs p = True
  | Nil, h => Void.exfalso h
  | Cons x xs, Inl px => rewrite px in rfl
  | Cons x xs, Inr h =>
    match c: p x with
      | True => rfl
      | False => List.anyOfAny p xs h

theorem List.anyIff (xs: List a) (p: a → Bool): List.any xs p = True ↔ List.Any (x => p x = True) xs :=
  { forward = List.anyToAny p xs, backward = List.anyOfAny p xs }

-- Membership written with `any` and `==` is `x ∈ xs`. (`x ∈ xs` as a
-- `Bool` is `List.decMem`'s decision: `Decidable.toBoolSound` and
-- `Decidable.toBoolOf` take it to the proposition and back.)
theorem List.anyEqIff [auto eq: DecEq a] (x: a) (xs: List a): List.any xs (== x) = True ↔ x ∈ xs := {
  forward = h => List.anyTrueElim xs (== x) (x ∈ xs) h (y m e => rewrite <- DecEq.sound y x e in m),
  backward = m => List.anyOfMem xs (== x) x (DecEq.refl x) m
}

theorem List.allIffExample: List.All (x => Nat.leq 1 x = True) [1, 2, 3] := (List.allIff [1, 2, 3] (x => Nat.leq 1 x)).forward rfl

-- `any` is whether `find` finds something.
theorem List.anyFind (p: a → Bool): (xs: List a) → List.any xs p = Option.isSome (List.find xs p)
  | Nil => rfl
  | Cons x xs =>
    match c: p x with
      | True => rfl
      | False => List.anyFind p xs

-- Running accumulations beside the elements: `List.zipWith xs
-- (List.scanLeft xs z f) g` is `g` of each element and the fold of the
-- elements before it (`List.getOrZipWithScanLeft`, std/List/Index.sw). It
-- lays items end to end from `z`, say, with `f` adding an item's size and
-- `g` placing it. Its first step, for induction, is by computation:
theorem List.zipWithScanLeftCons (x: a) (xs: List a) (z: b) (f: b → a → b) (g: a → b → c):
    List.zipWith (Cons x xs) (List.scanLeft (Cons x xs) z f) g = Cons (g x z) (List.zipWith xs (List.scanLeft xs (f z x) f) g) := rfl

theorem List.zipWithScanLeftExample:
    List.zipWith [2, 3, 4] (List.scanLeft [2, 3, 4] 10 (offset width => offset + width)) (width offset => (offset, width)) = [(10, 2), (12, 3), (15, 4)] := rfl

-- It has an element for each element.
theorem List.lengthZipWithScanLeft (f: b → a → b) (g: a → b → c): (xs: List a) → (z: b) →
    List.length (List.zipWith xs (List.scanLeft xs z f) g) = List.length xs
  | Nil, z => rfl
  | Cons x xs, z => Eq.cong Succ (List.lengthZipWithScanLeft f g xs (f z x))

-- What `g` keeps of an element (`h`, an id say) doesn't depend on the other
-- list, so mapping it over the zip is mapping over the first list.
theorem List.mapZipWithLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x):
    (xs: List a) → (ys: List b) → List.length xs ≤ List.length ys → List.map (List.zipWith xs ys g) h = List.map xs k
  | Nil, ys, le => rfl
  | Cons x xs, Nil, le => Void.exfalso (Bool.falseNotTrue le)
  | Cons x xs, Cons y ys, le => rewrite same x y, List.mapZipWithLeft h k g same xs ys le in rfl

theorem List.mapZipWithScanLeft (h: c → d) (k: a → d) (g: a → b → c) (same: (x: a) → (y: b) → h (g x y) = k x)
    (xs: List a) (z: b) (f: b → a → b): List.map (List.zipWith xs (List.scanLeft xs z f) g) h = List.map xs k :=
  List.mapZipWithLeft h k g same xs (List.scanLeft xs z f) (rewrite List.lengthScanLeft xs z f in Nat.leSucc (List.length xs))

-- `mapAccumLeft` is a fold for its final state, and for its list the zip of
-- the elements with the running states.
theorem List.mapAccumLeftGoSpec (f: s → a → Pair s b): (xs: List a) → (state: s) → (done: List b) →
    List.mapAccumLeftGo f state done xs
      = MkPair (List.foldLeft xs state (st x => Pair.fst (f st x)))
        (List.reverseOnto done (List.zipWith xs (List.scanLeft xs state (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x))))
  | Nil, state, done => rfl
  | Cons x xs, state, done => List.mapAccumLeftGoSpec f xs (Pair.fst (f state x)) (Cons (Pair.snd (f state x)) done)

theorem List.mapAccumLeftState (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.fst (List.mapAccumLeft xs initial f) = List.foldLeft xs initial (st x => Pair.fst (f st x)) :=
  Eq.cong Pair.fst (List.mapAccumLeftGoSpec f xs initial Nil)

theorem List.mapAccumLeftList (xs: List a) (initial: s) (f: s → a → Pair s b):
    Pair.snd (List.mapAccumLeft xs initial f) = List.zipWith xs (List.scanLeft xs initial (st x => Pair.fst (f st x))) (x st => Pair.snd (f st x)) :=
  Eq.cong Pair.snd (List.mapAccumLeftGoSpec f xs initial Nil)

theorem List.lengthMapAccumLeft (xs: List a) (initial: s) (f: s → a → Pair s b):
    List.length (Pair.snd (List.mapAccumLeft xs initial f)) = List.length xs :=
  rewrite List.mapAccumLeftList xs initial f in List.lengthZipWithScanLeft (st x => Pair.fst (f st x)) (x st => Pair.snd (f st x)) xs initial

theorem List.mapAccumLeftExample: List.mapAccumLeft [1, 2, 3] 0 (sum x => MkPair (sum + x) sum) = MkPair 6 [0, 1, 3] := rfl

-- `List.get`, the element at an index if there is one: it is `Some` exactly
-- within the list, what it finds is an element, and it goes through `map`,
-- `zipWith`, `append` and `take`. (`List.getOrGet`, std/List/Index.sw, is
-- `List.getOr` from it.)

-- `get` finds something exactly when the index is within the list.
theorem List.isSomeGet: (xs: List a) → (k: Nat) → Option.isSome (List.get xs k) = Nat.leq (Succ k) (List.length xs)
  | Nil, k => rfl
  | Cons x xs, Zero => rfl
  | Cons x xs, Succ k => List.isSomeGet xs k

theorem List.getInRange (xs: List a) (k: Nat): k < List.length xs ↔ Option.isSome (List.get xs k) = True := {
  forward = h => Eq.trans (List.isSomeGet xs k) h,
  backward = h => Eq.trans (Eq.sym (List.isSomeGet xs k)) h
}

-- Past the end, `get` finds nothing.
theorem List.getPast: (xs: List a) → (k: Nat) → List.length xs ≤ k → List.get xs k = None
  | Nil, k, h => rfl
  | Cons x xs, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ k, h => List.getPast xs k h

-- What `get` finds is an element of the list.
theorem List.memOfGet: (xs: List a) → (k: Nat) → (v: a) → List.get xs k = Some v → v ∈ xs
  | Nil, k, v, h => Void.exfalso (Option.noneNotSome v h)
  | Cons x xs, Zero, v, h => Inl (Option.someInjective x v h)
  | Cons x xs, Succ k, v, h => Inr (List.memOfGet xs k v h)

theorem List.getMap: (xs: List a) → (f: a → b) → (k: Nat) → List.get (List.map xs f) k = Option.map (List.get xs k) f
  | Nil, f, k => rfl
  | Cons x xs, f, Zero => rfl
  | Cons x xs, f, Succ k => List.getMap xs f k

-- `zipWith` has `f x y` where both lists have an element, `x` and `y`.
theorem List.getZipWith (f: a → b → c): (xs: List a) → (ys: List b) → (k: Nat) →
    List.get (List.zipWith xs ys f) k = Option.flatMap (List.get xs k) (x => Option.map (List.get ys k) (f x))
  | Nil, ys, k => rfl
  | Cons x xs, Nil, Zero => rfl
  | Cons x xs, Nil, Succ k =>
    match c: List.get xs k with
      | None => rfl
      | Some u => rfl
  | Cons x xs, Cons y ys, Zero => rfl
  | Cons x xs, Cons y ys, Succ k => List.getZipWith f xs ys k

-- `append`: the first list's element, else the second's, counting on from
-- the end of the first.
theorem List.getAppend: (xs: List a) → (ys: List a) → (k: Nat) →
    List.get (List.append xs ys) k = Option.orElse (List.get xs k) (List.get ys (k - List.length xs))
  | Nil, ys, k => rfl
  | Cons x xs, ys, Zero => rfl
  | Cons x xs, ys, Succ k => List.getAppend xs ys k

theorem List.getAppendLeft: (xs: List a) → (ys: List a) → (k: Nat) → k < List.length xs → List.get (List.append xs ys) k = List.get xs k
  | Nil, ys, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, ys, Zero, h => rfl
  | Cons x xs, ys, Succ k, h => List.getAppendLeft xs ys k h

theorem List.getAppendRight: (xs: List a) → (ys: List a) → (k: Nat) → List.length xs ≤ k →
    List.get (List.append xs ys) k = List.get ys (k - List.length xs)
  | Nil, ys, k, h => rfl
  | Cons x xs, ys, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, ys, Succ k, h => List.getAppendRight xs ys k h

-- `take n` keeps the elements before `n`, and nothing from `n` on.
theorem List.getTake: (xs: List a) → (n: Nat) → (k: Nat) → k < n → List.get (List.take xs n) k = List.get xs k
  | xs, Zero, k, h => Void.exfalso (Bool.falseNotTrue h)
  | Nil, Succ n, k, h => rfl
  | Cons x xs, Succ n, Zero, h => rfl
  | Cons x xs, Succ n, Succ k, h => List.getTake xs n k h

theorem List.getTakePast: (xs: List a) → (n: Nat) → (k: Nat) → n ≤ k → List.get (List.take xs n) k = None
  | xs, Zero, k, h => rfl
  | Nil, Succ n, k, h => rfl
  | Cons x xs, Succ n, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ n, Succ k, h => List.getTakePast xs n k h

theorem List.getExample: List.get (List.append [1, 2] (List.map [3, 4] Succ)) 3 = Some 5 := rfl

-- For any list of successors, what `get` finds is not zero.
theorem List.getMapExample (xs: List Nat) (k: Nat) (v: Nat) (h: List.get (List.map xs Succ) k = Some v): Not (v = 0) :=
  Option.mapEqSome (List.get xs k) Succ v (Eq.trans (Eq.sym (List.getMap xs Succ k)) h) (u found e => rewrite <- e in Nat.succNotZero u)
