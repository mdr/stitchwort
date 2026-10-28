-- The list toolkit: `map`, `filter`, folds, sums, `zip`, `take`/`drop`, `get`,
-- `splitBy`, padding, transpose and the like, with the congruence lemmas that
-- `decreasing` and `rewrite` look up beside each function. The other lemmas
-- are in List/Lemmas.sw, so a program that only calls these checks none of them.

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

-- `f` on each element, in order, for what it performs: `rows.forEach (row =>
-- Fail.ensure …)` checks every row, stopping at the first that fails.
def List.forEach: List a → (f: a → {e} ()) → {e} ()
  | Nil, f => ()
  | Cons x xs, f =>
    f x
    List.forEach xs f

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

-- Right fold. `List.foldRight [x, y] initial f` is `f x (f y initial)`. Runs
-- as a loop over the reversed list, so it is stack-safe on long lists. `f`
-- may perform abilities, which run last element first, as the definition
-- reads: `f y initial` is computed before `f x …`.
def List.foldRight (xs: List a) (initial: b) (f: a → b → {e} b): {e} b := List.foldLeft (List.reverseOnto xs Nil) initial (acc x => f x acc)

-- The sum of the elements, of any type with `Add` (docs/proposals/interfaces.md
-- §7.7): `[1, 2, 3].sum` is `6`, `[3, -5, 1].sum` is `-1`.
def List.sum [auto add: Add a] (xs: List a): a := List.foldLeft xs Add.zero Add.add

-- The sum of `f` over the elements: `List.sumBy xs f` is `List.sum (List.map xs f)`
-- without building the intermediate list. `f` may perform abilities, which
-- run in list order.
def List.sumBy [auto add: Add b] (xs: List a) (f: a → {e} b): {e} b := List.foldLeft xs Add.zero (acc x => acc + f x)

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

-- Combines four lists up to the shortest list's length.
def List.zipWith4: List a → List b → List c → List d → (f: a → b → c → d → e) → List e
  | Nil, ys, zs, ws, f => Nil
  | Cons x xs, Nil, zs, ws, f => Nil
  | Cons x xs, Cons y ys, Nil, ws, f => Nil
  | Cons x xs, Cons y ys, Cons z zs, Nil, f => Nil
  | Cons x xs, Cons y ys, Cons z zs, Cons w ws, f => Cons (f x y z w) (List.zipWith4 xs ys zs ws f)

-- Each element paired with the next: `[1, 2, 3].zipWithNext` is
-- `[(1, 2), (2, 3)]`, empty for fewer than two elements.
def List.zipWithNext: List a → List (Pair a a)
  | Nil => Nil
  | Cons x Nil => Nil
  | Cons x (Cons next rest) => Cons (MkPair x next) (List.zipWithNext (Cons next rest))

-- Whether `holds` is true of each element and the next:
-- `[1, 2, 4].chain (x y => x < y)` is true. True for fewer than two elements.
-- `List.Sorted le xs` says the same as a `Prop` (`List.sortedOfChain`).
def List.chain: List a → (holds: a → a → Bool) → Bool
  | Nil, holds => True
  | Cons x Nil, holds => True
  | Cons x (Cons next rest), holds => holds x next ∧ List.chain (Cons next rest) holds

-- Tests that agree on every pair give the same answer.
theorem List.chainCong: (xs: List a) → (holds1: a → a → Bool) → (holds2: a → a → Bool) → ((x: a) → (y: a) → holds1 x y = holds2 x y) →
    List.chain xs holds1 = List.chain xs holds2
  | Nil, holds1, holds2, eh => rfl
  | Cons x Nil, holds1, holds2, eh => rfl
  | Cons x (Cons next rest), holds1, holds2, eh => rewrite eh x next, List.chainCong (Cons next rest) holds1 holds2 eh

test "List.zipWithNext" := List.zipWithNext [1, 2, 3] == [MkPair 1 2, MkPair 2 3] ∧ List.zipWithNext [7] == Nil ∧ List.zipWithNext (Nil: List Nat) == Nil
test "List.chain" := List.chain [1, 2, 4] (x y => x < y) ∧ ¬(List.chain [1, 3, 2] (x y => x < y)) ∧ List.chain [5] (x y => x < y)

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

-- `List.range n` is `[0, 1, ..., n - 1]`.
def List.range (n: Nat): List Nat := List.rangeFrom n 0

-- `List.between lo hi` is `[lo, lo + 1, ..., hi]`, both ends included; empty
-- when `lo > hi`.
def List.between (lo: Nat) (hi: Nat): List Nat := List.rangeFrom (hi + 1 - lo) lo
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

-- All but the last element (`Nil` for an empty list).
def List.init: List a → List a
  | Nil => Nil
  | Cons x Nil => Nil
  | Cons x (Cons y ys) => Cons x (List.init (Cons y ys))

-- Membership, given a decision for equality (as `List.decEq` takes).
def List.elem: List a → (target: a) → (decEq: (x: a) → (y: a) → Decidable (x = y)) → Bool
  | Nil, target, decEq => False
  | Cons x xs, target, decEq => if Decidable.toBool (decEq target x) then True else List.elem xs target decEq

-- Whether `x` is on the list, by its `DecEq` (`List.memContains` says it is
-- membership).
def List.contains [auto eq: DecEq a] (xs: List a) (x: a): Bool := List.any xs (member => member == x)

-- Whether the list has no elements.
def List.isEmpty: List a → Bool
  | Nil => True
  | Cons x xs => False

-- Whether `xs` begins with `prefix`. Every list starts with `[]`.
def List.startsWith [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → Bool
  | xs, Nil => True
  | Nil, Cons p ps => False
  | Cons x xs, Cons p ps => x == p && List.startsWith xs ps

-- The rest of `xs` after `prefix`, or `None` if `xs` doesn't start with it.
-- The empty prefix gives `Some xs`.
def List.stripPrefix [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → Option (List a)
  | xs, Nil => Some xs
  | Nil, Cons p ps => None
  | Cons x xs, Cons p ps => if x == p then List.stripPrefix xs ps else None

test "List.isEmpty" := List.isEmpty (Nil: List Nat) ∧ ¬(List.isEmpty [3])
test "List.startsWith" := List.startsWith [1, 2, 3] [1, 2] ∧ List.startsWith [1, 2] [] ∧ ¬(List.startsWith [1, 2] [1, 3]) ∧ ¬(List.startsWith [1] [1, 2])
test "List.stripPrefix" :=
  List.stripPrefix [1, 2, 3] [1, 2] == Some [3] ∧ List.stripPrefix [1, 2] [] == Some [1, 2] ∧ List.stripPrefix [1, 2] [2] == None
    ∧ List.stripPrefix [1] [1, 2] == None

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

test "List.partition" := List.partition [1, 5, 2, 7] (x => x > 4) == MkPair [5, 7] [1, 2] ∧ List.partition (Nil: List Nat) (x => x > 4) == MkPair Nil Nil

-- The value for the first pair whose key equals `key`.
def List.lookup [auto eq: DecEq k]: List (Pair k v) → (key: k) → Option v
  | Nil, key => None
  | Cons (MkPair entryKey value) rest, key => if entryKey == key then Some value else rest.lookup key

-- `List.padRight xs n x` is `xs` followed by enough copies of `x` to make it
-- n long (it is `xs` itself when that is already n long or longer).
def List.padRight (xs: List a) (n: Nat) (x: a): List a := xs.append (List.replicate (n - xs.length) x)

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

-- Every row has length n (the list is rectangular).
@[noReceiver]
def List.AllLength (n: Nat): List (List a) → Prop
  | Nil => Unit
  | Cons r rs => And (List.length r = n) (List.AllLength n rs)

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

-- Adds a group to the finished ones, unless it is empty.
def List.closeGroup: List a → List (List a) → List (List a)
  | Nil, done => done
  | Cons y ys, done => Cons (Cons y ys) done

def List.splitTotal (st: Pair (List a) (List (List a))): Nat := List.length (Pair.fst st) + List.sumBy (Pair.snd st) List.length

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

@[noReceiver]
def List.SplitKeeps (p: a → Bool) (xs: List a) (st: Pair (List a) (List (List a))): Prop :=
  List.append (Pair.fst st) (List.concat (Pair.snd st)) = List.filter xs (x => ¬(p x))

test "List.splitBy with separators on the end" :=
  [1, 0, 2].splitBy (== 0) == [[1], [2]] ∧ [1, 0, 2, 0, 0].splitBy (== 0) == [[1], [2]] ∧ [0, 0].splitBy (== 0) == Nil

-- How many elements satisfy `p` (as `List.count`, but recursing on the list,
-- which suits proofs).
def List.occurrences: List a → (p: a → Bool) → Nat
  | Nil, p => 0
  | Cons x xs, p => Bool.toNat (p x) + List.occurrences xs p

-- `xs` and `ys` are permutations of each other: every test is passed by as
-- many elements of one as of the other. For elements with decidable equality
-- this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
-- turns the proofs into arithmetic, and needs no equality on the elements.
def List.Perm (xs: List a) (ys: List a): Prop := (p: a → Bool) → List.occurrences xs p = List.occurrences ys p

-- `s` is `xs` with some elements left out, the rest kept in order: each
-- element of `s` is matched with an element of `xs`, or `xs`'s first element
-- is skipped.
def List.Subsequence: List a → List a → Prop
  | Nil, ys => Unit
  | Cons x xs, Nil => Void
  | Cons x xs, Cons y ys => Or (And (x = y) (List.Subsequence xs ys)) (List.Subsequence (Cons x xs) ys)

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

theorem List.anyCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.any xs p1 = List.any xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x, List.anyCong xs p1 p2 ep

theorem List.allCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.all xs p1 = List.all xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x, List.allCong xs p1 p2 ep

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

-- The run `List.rangeFrom c s` holds the numbers from `s` up to, not
-- including, `s + c`.
theorem List.memRangeFrom (x: Nat): (c: Nat) → (s: Nat) → x ∈ List.rangeFrom c s → And (s ≤ x) (x < s + c)
  | Zero, s, h => Void.exfalso h
  | Succ c, s, Inl q => rewrite <- q in Both (Nat.leRefl s) (Nat.ltAddSuccSelf s c)
  | Succ c, s, Inr m =>
    match List.memRangeFrom x c (Succ s) m with
      | Both lo hi => Both (Nat.lessLe s x lo) (Nat.ltAddSucc s c x hi)

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

-- Without the element at `index`, counting from 0 (the same list if there is
-- none): `[1, 2, 3].removeAt 1` is `[1, 3]`.
def List.removeAt: List a → Nat → List a
  | Nil, index => Nil
  | Cons x xs, Zero => xs
  | Cons x xs, Succ index => Cons x (List.removeAt xs index)

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

-- `f` of each element's index and the element:
-- `["a", "b"].mapWithIndex (index x => "${index}${x}")` is `["0a", "1b"]`.
def List.mapWithIndex (xs: List a) (f: Nat → a → {e} b): {e} List b := xs.withIndex.map (pair => f pair.fst pair.snd)

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
test "List.mapWithIndex" := ["a", "b"].mapWithIndex (index x => "${index}${x}") == ["0a", "1b"] ∧ (Nil: List Nat).mapWithIndex (index x => index + x) == Nil
test "List.mapWithIndex is withIndex then map" := [5, 6, 7].mapWithIndex (index x => index * x) == [5, 6, 7].withIndex.map (((index, x)) => index * x)
test "List.findMap" := [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == Some 30 ∧ [1].findMap (x => (None: Option Nat)) == None
test "List.findMap is the head of filterMap" :=
  [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == ([1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 10) else None)).head ∧
    [1].findMap (x => (None: Option Nat)) == ([1].filterMap (x => (None: Option Nat))).head
test "List.between" := List.between 2 5 == [2, 3, 4, 5] ∧ List.between 3 3 == [3] ∧ List.between 4 2 == Nil ∧ List.between 0 1 == [0, 1]
test "List.flatMap" := [1, 2, 3].flatMap (x => List.replicate x x) == [1, 2, 2, 3, 3, 3]
test "List.contains" := [1, 2, 3].contains 2 ∧ ¬([1, 2, 3].contains 4) ∧ ¬((Nil: List Nat).contains 1)
test "List.pairs" := [1, 2, 3].pairs == [MkPair 1 2, MkPair 1 3, MkPair 2 3] ∧ (Nil: List Nat).pairs == Nil ∧ [1].pairs == (Nil: List (Pair Nat Nat))
test "List.pairs count" := List.length (List.range 10).pairs == 45
test "List.cross" := [1, 2].cross ["a", "b"] == [MkPair 1 "a", MkPair 1 "b", MkPair 2 "a", MkPair 2 "b"] ∧ [1].cross (Nil: List Nat) == Nil

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

theorem List.allCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.all xs p1 = List.all xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x (Inl rfl), List.allCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.occurrencesCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) →
    List.occurrences xs p1 = List.occurrences xs p2
  | Nil, p1, p2, ep => rfl
  | Cons x xs, p1, p2, ep => rewrite ep x (Inl rfl), List.occurrencesCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.foldLeftCongMem: (xs: List a) → (z: b) → (f1: b → a → b) → (f2: b → a → b) → ((acc: b) → (x: a) → (m: x ∈ xs) → f1 acc x = f2 acc x) →
    List.foldLeft xs z f1 = List.foldLeft xs z f2
  | Nil, z, f1, f2, ef => rfl
  | Cons x xs, z, f1, f2, ef =>
    Eq.trans (Eq.cong (t => List.foldLeft xs t f1) (ef z x (Inl rfl))) (List.foldLeftCongMem xs (f2 z x) f1 f2 (acc y m => ef acc y (Inr m)))

theorem List.filterMapCongMem: (xs: List a) → (f1: a → Option b) → (f2: a → Option b) → ((x: a) → (m: x ∈ xs) → f1 x = f2 x) →
    List.filterMap xs f1 = List.filterMap xs f2
  | Nil, f1, f2, ef => rfl
  | Cons x xs, f1, f2, ef => rewrite ef x (Inl rfl), List.filterMapCongMem xs f1 f2 (y m => ef y (Inr m))

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

theorem List.allCongRange (p1: Nat → Bool) (p2: Nat → Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → p1 x = p2 x):
    List.all (List.rangeFrom c s) p1 = List.all (List.rangeFrom c s) p2 :=
  List.allCongMem (List.rangeFrom c s) p1 p2 (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.occurrencesCongRange (p1: Nat → Bool) (p2: Nat → Bool) (c: Nat) (s: Nat)
    (ep: (x: Nat) → (low: s ≤ x) → (high: x < s + c) → p1 x = p2 x):
    List.occurrences (List.rangeFrom c s) p1 = List.occurrences (List.rangeFrom c s) p2 :=
  List.occurrencesCongMem (List.rangeFrom c s) p1 p2 (x m => ep x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

theorem List.foldLeftCongRange (f1: b → Nat → b) (f2: b → Nat → b) (z: b) (c: Nat) (s: Nat)
    (ef: (acc: b) → (x: Nat) → (low: s ≤ x) → (high: x < s + c) → f1 acc x = f2 acc x):
    List.foldLeft (List.rangeFrom c s) z f1 = List.foldLeft (List.rangeFrom c s) z f2 :=
  List.foldLeftCongMem (List.rangeFrom c s) z f1 f2
    (acc x m => ef acc x (And.left (List.memRangeFrom x c s m)) (And.right (List.memRangeFrom x c s m)))

-- `sumBy` and `count` are folds, so their congruence lemmas are the fold's.
theorem List.sumByCongRange [auto add: Add c] (f: Nat → c) (g: Nat → c): (c: Nat) → (s: Nat) → ((x: Nat) → s ≤ x → x < s + c → f x = g x) →
    List.sumBy (List.rangeFrom c s) f = List.sumBy (List.rangeFrom c s) g :=
  c s h => List.foldLeftCongRange (acc x => acc + f x) (acc x => acc + g x) Add.zero c s (acc x low high => Eq.cong (t => acc + t) (h x low high))

theorem List.countCongMem (xs: List a) (p1: a → Bool) (p2: a → Bool) (ep: (x: a) → (m: List.Mem x xs) → p1 x = p2 x): List.count xs p1 = List.count xs p2 :=
  List.foldLeftCongMem xs 0 (n x => Nat.succIf n (p1 x)) (n x => Nat.succIf n (p2 x)) (acc x m => Eq.cong (b => Nat.succIf acc b) (ep x m))
