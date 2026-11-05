--| The list toolkit: `map`, `filter`, folds, sums, `zip`, `take`/`drop`, `get`,
--| `splitBy`, padding, transpose and the like, with the congruence lemmas that
--| `decreasing` and `rewrite` look up beside each function. The other lemmas are
--| in List/Lemmas.sw, so a program that only calls these checks none of them.

--| List toolkit. Every function is structurally recursive.
--|
--| The callbacks of `map`, `filter`, `foldLeft`, `foldRight`, `sumBy`,
--| `count`, `any`, `all`, `find`, `filterMap`, `findMap`, `takeWhile`,
--| `flatMap`, `partition` and `span` may perform abilities, such as `Fail`,
--| `Log` or `Partial`. Their types say so with `{e}`: in `p: a → {e} Bool`,
--| `e` is the callback's row, and the result `{e} List a` performs the same.
--| With a pure callback the row is empty and `{e} b` is `b`, so each is the
--| plain function: its lemmas are about that, and the backends compile it to
--| the same loop. The other callbacks (`zipWith`, `scanLeft`, the sorts, …)
--| must be pure. With an effectful callback:
--| - the effects run in list order, first element first (`foldRight`'s run
--|   last to first, as its definition reads);
--| - the callback is called at most once per element;
--| - `any`, `all`, `find`, `findMap`, `takeWhile` and `span` stop calling it
--|   once the answer is decided.
-- (docs/proposals/effect-polymorphism.md and effect-polymorphic-list.md)

--| `f` on each element, in order: as long as the list ([`List.lengthMap`]). `f` may perform abilities, such as `Fail`:
--| `xs.map Range.read` fails at the first element that isn't a range. With a
--| pure `f` the row is empty and `{e} b` is `b`, so this is the plain map: its
--| lemmas are proved by computation as before, and the backends compile it to
--| the same loop.
-- (docs/proposals/errors.md §3.4)
def List.map: (xs: List a) → (f: a → {e} b) → {e} List b
  | [], f => []
  | [x, ..xs], f => [f x, ..List.map xs f]

--| `f` on each element, in order, for what it performs: `rows.forEach (row =>
--| Fail.ensure …)` checks every row, stopping at the first that fails.
@[tailrec]
def List.forEach: (xs: List a) → (f: a → {e} ()) → {e} ()
  | [], f => ()
  | [x, ..xs], f =>
    f x
    List.forEach xs f

--| One step of `List.filter`: `x` in front of the filtered rest, or not.
-- A function of its own so the recursive call is written once: with an `if`
-- around it in both branches, a condition the checker can't decide (one on a
-- variable) keeps both branches, and the value doubles with every element.
@[noReceiver]
def List.filterStep (x: a) (rest: List a): (keep: Bool) → List a
  | True => [x, ..rest]
  | False => rest

--| The elements satisfying `p`, in order ([`List.memFilter`]; there are `List.count xs p` of them,
--| [`List.lengthFilter`]). `p` may perform abilities: it runs on
--| each element once, in list order (the `let` runs it before the rest of the
--| list is filtered), so a `Fail` reports the first bad element.
def List.filter: (xs: List a) → (p: a → {e} Bool) → {e} List a
  | [], p => []
  | [x, ..xs], p =>
    let keep := p x
    List.filterStep x (List.filter xs p) keep

--| Left fold, tail-recursive: `List.foldLeft [x, y] initial f` is `f (f initial x) y`.
--| `f` may perform abilities, which run in list order.
@[tailrec]
def List.foldLeft: (xs: List a) → (initial: b) → (f: b → a → {e} b) → {e} b
  | [], initial, f => initial
  | [x, ..xs], initial, f => List.foldLeft xs (f initial x) f

--| Running accumulations, the initial value first (Haskell's `scanLeft`):
--| `List.scanLeft [x, y] initial f` is `[initial, f initial x, f (f initial x) y]`. Always one longer than
--| the input.
def List.scanLeft: (xs: List a) → (initial: b) → (f: b → a → b) → List b
  | [], initial, f => [initial]
  | [x, ..xs], initial, f => [initial, ..List.scanLeft xs (f initial x) f]

--| Right fold: `List.foldRight [x, y] initial f` is `f x (f y initial)`. Runs
--| as a loop over the reversed list, so it is stack-safe on long lists. `f`
--| may perform abilities, which run last element first, as the definition
--| reads: `f y initial` is computed before `f x …`.
def List.foldRight (xs: List a) (initial: b) (f: a → b → {e} b): {e} b := List.foldLeft (List.reverseOnto xs []) initial (acc x => f x acc)

--| The sum of the elements, of any type with `Add`: `[1, 2, 3].sum` is `6`,
--| `[3, -5, 1].sum` is `-1`. The sum of a join is the sum of the sums ([`List.sumAppend`]).
-- (docs/proposals/interfaces.md §7.7)
def List.sum [auto add: Add a] (xs: List a): a := List.foldLeft xs Add.zero Add.add

--| The sum of `f` over the elements: `List.sumBy xs f` is
--| `List.sum (List.map xs f)` without building the intermediate list. `f` may
--| perform abilities, which run in list order.
def List.sumBy [auto add: Add b] (xs: List a) (f: a → {e} b): {e} b := List.foldLeft xs Add.zero (acc x => acc + f x)

--| The product of the elements, of any type with `Mul`.
def List.product [auto mul: Mul a] (xs: List a): a := List.foldLeft xs Mul.one Mul.mul

--| The largest element by the type's `Ord`, or `None` for an empty list.
def List.maximum [auto ord: Ord a]: (xs: List a) → Option a
  | [] => None
  | [x, ..xs] => Some (List.foldLeft xs x Ord.max)

--| The smallest element by the type's `Ord`, or `None` for an empty list.
def List.minimum [auto ord: Ord a]: (xs: List a) → Option a
  | [] => None
  | [x, ..xs] => Some (List.foldLeft xs x Ord.min)

--| The elements of two lists paired up, up to the shorter list's length: `[1, 2, 3].zip ["a", "b"]` is `[(1, "a"), (2, "b")]`.
def List.zip: (xs: List a) → (ys: List b) → List (Pair a b)
  | [], ys => []
  | [x, ..xs], [] => []
  | [x, ..xs], [y, ..ys] => [MkPair x y, ..List.zip xs ys]

--| `f` of the elements of two lists, pair by pair, up to the shorter list's length ([`List.lengthZipWithLe`]).
def List.zipWith: (xs: List a) → (ys: List b) → (f: a → b → c) → List c
  | [], ys, f => []
  | [x, ..xs], [], f => []
  | [x, ..xs], [y, ..ys], f => [f x y, ..List.zipWith xs ys f]

--| Combines three lists up to the shortest list's length.
def List.zipWith3: (xs: List a) → (ys: List b) → (zs: List c) → (f: a → b → c → d) → List d
  | [], ys, zs, f => []
  | [x, ..xs], [], zs, f => []
  | [x, ..xs], [y, ..ys], [], f => []
  | [x, ..xs], [y, ..ys], [z, ..zs], f => [f x y z, ..List.zipWith3 xs ys zs f]

--| Combines four lists up to the shortest list's length.
def List.zipWith4: (xs: List a) → (ys: List b) → (zs: List c) → (ws: List d) → (f: a → b → c → d → e) → List e
  | [], ys, zs, ws, f => []
  | [x, ..xs], [], zs, ws, f => []
  | [x, ..xs], [y, ..ys], [], ws, f => []
  | [x, ..xs], [y, ..ys], [z, ..zs], [], f => []
  | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], f => [f x y z w, ..List.zipWith4 xs ys zs ws f]

--| Each element paired with the next: `[1, 2, 3].zipWithNext` is
--| `[(1, 2), (2, 3)]`, empty for fewer than two elements.
def List.zipWithNext: (xs: List a) → List (Pair a a)
  | [] => []
  | [x] => []
  | [x, next, ..rest] => [MkPair x next, ..List.zipWithNext [next, ..rest]]

--| Whether `holds` is true of each element and the next:
--| `[1, 2, 4].chain (x y => x < y)` is true. True for fewer than two elements.
--| `List.Sorted le xs` says the same as a `Prop` ([`List.sortedOfChain`]).
@[tailrec]
def List.chain: (xs: List a) → (holds: a → a → Bool) → Bool
  | [], holds => True
  | [x], holds => True
  | [x, next, ..rest], holds => holds x next ∧ List.chain [next, ..rest] holds

--| Tests that agree on every pair give the same answer.
theorem List.chainCong: (xs: List a) → (holds1: a → a → Bool) → (holds2: a → a → Bool) → ((x: a) → (y: a) → holds1 x y = holds2 x y) →
    List.chain xs holds1 = List.chain xs holds2
  | [], holds1, holds2, eh => rfl
  | [x], holds1, holds2, eh => rfl
  | [x, next, ..rest], holds1, holds2, eh => rewrite eh x next, List.chainCong [next, ..rest] holds1 holds2 eh

test "List.zipWithNext" := List.zipWithNext [1, 2, 3] == [MkPair 1 2, MkPair 2 3] ∧ List.zipWithNext [7] == [] ∧ List.zipWithNext ([]: List Nat) == []
test "List.chain" := List.chain [1, 2, 4] (x y => x < y) ∧ ¬(List.chain [1, 3, 2] (x y => x < y)) ∧ List.chain [5] (x y => x < y)

--| The first n elements (all of them if there are fewer): n of them when the list is long enough ([`List.lengthTake`]).
def List.take: (xs: List a) → (count: Nat) → List a
  | xs, Zero => []
  | [], Succ n => []
  | [x, ..xs], Succ n => [x, ..List.take xs n]

--| All but the first n elements; after `List.take` of the same n, the whole list ([`List.appendTakeDrop`]).
@[tailrec]
def List.drop: (xs: List a) → (count: Nat) → List a
  | xs, Zero => xs
  | [], Succ n => []
  | [x, ..xs], Succ n => List.drop xs n

--| The element at index i, counting from 0, or `None` past the end.
@[tailrec]
def List.get: (xs: List a) → (index: Nat) → Option a
  | [], i => None
  | [x, ..xs], Zero => Some x
  | [x, ..xs], Succ i => List.get xs i

--| Whether some element satisfies `p`. `p` may perform abilities: it runs in
--| list order and isn't called after the first element that satisfies it.
@[tailrec]
def List.any: (xs: List a) → (p: a → {e} Bool) → {e} Bool
  | [], p => False
  | [x, ..xs], p => if p x then True else List.any xs p

--| Whether every element satisfies `p`. `p` may perform abilities: it runs in
--| list order and isn't called after the first element that fails it.
@[tailrec]
def List.all: (xs: List a) → (p: a → {e} Bool) → {e} Bool
  | [], p => True
  | [x, ..xs], p => if p x then List.all xs p else False

--| `n`, plus one if `b`: `List.count`'s step.
-- A function of its own so `n` is written once: `if b then Succ n else n`
-- writes it twice, so when the checker can't decide the conditions, a count
-- doubles in size with every element.
def Nat.succIf (n: Nat): (cond: Bool) → Nat
  | True => Succ n
  | False => n

--| How many elements satisfy `p`, at most the length ([`List.countLeLength`]).
--| `p` may perform abilities, which run in list order.
def List.count (xs: List a) (p: a → {e} Bool): {e} Nat := List.foldLeft xs 0 (n x => Nat.succIf n (p x))

--| The first element satisfying `p`, which is in the list ([`List.findSome`]).
--| `p` may perform abilities: it runs in list order and isn't called after the
--| element found.
@[tailrec]
def List.find: (xs: List a) → (p: a → {e} Bool) → {e} Option a
  | [], p => None
  | [x, ..xs], p => if p x then Some x else List.find xs p

--| The list with the option's value in front, if it has one.
@[noReceiver]
def List.consSome: (item: Option b) → (rest: List b) → List b
  | None, rest => rest
  | Some y, rest => [y, ..rest]

--| Keeps the `Some` results, in order. `[1, 2, 3].filterMap (x => if x > 1 then Some (x * 10) else None)`
--| is `[20, 30]`. This is Scala's `collect`: `match some` writes the function as the cases to keep,
--| `lines.filterMap (match some | Corrupted illegal => illegal)`, and the lemma
--| [`List.memFilterMap`] says what is kept. `f` may perform abilities, which run in
--| list order (`f x` is the first argument, so it runs before the rest).
def List.filterMap: (xs: List a) → (f: a → {e} Option b) → {e} List b
  | [], f => []
  | [x, ..xs], f => List.consSome (f x) (List.filterMap xs f)

--| The values of the `Some` elements, in order, dropping the `None`s:
--| `[Some 1, None, Some 3].somes` is `[1, 3]`. It is `filterMap id`, so
--| [`List.memFilterMap`] applies, and [`List.memSomes`] says it directly.
def List.somes (xs: List (Option a)): List a := List.filterMap xs id

test "List.somes" := [Some 1, None, Some 3].somes == [1, 3] ∧ ([]: List (Option Nat)).somes == [] ∧ [None, None].somes == ([]: List Nat)

--| Joins a list of lists, in order: `[[1, 2], [], [3]].concat` is `[1, 2, 3]`.
def List.concat: (xss: List (List a)) → List a
  | [] => []
  | [xs, ..xss] => List.append xs (List.concat xss)

--| n copies of `x`: `List.replicate 3 'a'` is `['a', 'a', 'a']` ([`List.lengthReplicate`]).
def List.replicate: (count: Nat) → (x: a) → List a
  | Zero, x => []
  | Succ n, x => [x, ..List.replicate n x]

--| `n` numbers counting up from `i`: `List.rangeFrom 3 5` is `[5, 6, 7]` ([`List.lengthRangeFrom`]).
def List.rangeFrom (count: Nat) (start: Nat): List Nat :=
  match count with
    | Zero => []
    | Succ n => [start, ..List.rangeFrom n (Succ start)]

--| The numbers from 0 up to, not including, `n`: `List.range 3` is `[0, 1, 2]`.
def List.range (n: Nat): List Nat := List.rangeFrom n 0

--| `List.between lo hi` is `[lo, lo + 1, ..., hi]`, both ends included; empty
--| when `lo > hi`.
def List.between (lo: Nat) (hi: Nat): List Nat := List.rangeFrom (hi + 1 - lo) lo
test "List.between, empty and single" := List.between 5 0 == [] ∧ List.between 0 0 == [0] ∧ List.between 7 7 == [7]

--| The elements in the opposite order: reversing twice gives the list back ([`List.reverseReverse`]).
def List.reverse (xs: List a): List a := List.reverseOnto xs []

--| The last element, or `None` for an empty list.
@[tailrec]
def List.last: (xs: List a) → Option a
  | [] => None
  | [x] => Some x
  | [x, y, ..ys] => List.last [y, ..ys]

--| The first element, or `None` for an empty list.
def List.head: (xs: List a) → Option a
  | [] => None
  | [x, ..xs] => Some x

--| All but the last element (`Nil` for an empty list).
def List.init: (xs: List a) → List a
  | [] => []
  | [x] => []
  | [x, y, ..ys] => [x, ..List.init [y, ..ys]]

--| Membership, given a decision for equality (as `List.decEq` takes).
@[tailrec]
def List.elem: (xs: List a) → (target: a) → (decEq: (x: a) → (y: a) → Decidable (x = y)) → Bool
  | [], target, decEq => False
  | [x, ..xs], target, decEq => if Decidable.toBool (decEq target x) then True else List.elem xs target decEq

--| Whether `x` is on the list, by its `DecEq` ([`List.memContains`] says it is
--| membership).
def List.contains [auto eq: DecEq a] (xs: List a) (x: a): Bool := List.any xs (member => member == x)

--| Whether the list has no elements.
def List.isEmpty: (xs: List a) → Bool
  | [] => True
  | [x, ..xs] => False

--| Whether `xs` begins with `prefix`. Every list starts with `[]`.
@[tailrec]
def List.startsWith [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → Bool
  | xs, [] => True
  | [], [p, ..ps] => False
  | [x, ..xs], [p, ..ps] => x == p && List.startsWith xs ps

--| The rest of `xs` after `prefix`, or `None` if `xs` doesn't start with it.
--| The empty prefix gives `Some xs`.
@[tailrec]
def List.stripPrefix [auto eq: DecEq a]: (xs: List a) → (prefix: List a) → Option (List a)
  | xs, [] => Some xs
  | [], [p, ..ps] => None
  | [x, ..xs], [p, ..ps] => if x == p then List.stripPrefix xs ps else None

test "List.isEmpty" := List.isEmpty ([]: List Nat) ∧ ¬(List.isEmpty [3])
test "List.startsWith" := List.startsWith [1, 2, 3] [1, 2] ∧ List.startsWith [1, 2] [] ∧ ¬(List.startsWith [1, 2] [1, 3]) ∧ ¬(List.startsWith [1] [1, 2])
test "List.stripPrefix" :=
  List.stripPrefix [1, 2, 3] [1, 2] == Some [3] ∧ List.stripPrefix [1, 2] [] == Some [1, 2] ∧ List.stripPrefix [1, 2] [2] == None
    ∧ List.stripPrefix [1] [1, 2] == None

--| One step of `List.partition`: `x` onto the kept or the dropped side of
--| `sides` (each reversed).
-- A function of its own so the recursive call is written once, as for
-- `List.filterStep`.
@[noReceiver]
def List.partitionStep (x: a) (sides: Pair (List a) (List a)): (keep: Bool) → Pair (List a) (List a)
  | True => MkPair [x, ..Pair.fst sides] (Pair.snd sides)
  | False => MkPair (Pair.fst sides) [x, ..Pair.snd sides]

--| `List.partition`'s loop: `sides` holds what has been sorted so far, each
--| side reversed.
@[noReceiver]
@[tailrec]
def List.partitionOnto (p: a → {e} Bool): (xs: List a) → (sides: Pair (List a) (List a)) → {e} Pair (List a) (List a)
  | [], sides => MkPair (List.reverse (Pair.fst sides)) (List.reverse (Pair.snd sides))
  | [x, ..xs], sides =>
    let keep := p x
    List.partitionOnto p xs (List.partitionStep x sides keep)

--| The elements that satisfy `p`, and those that don't, each in order: the
--| two `filter`s ([`List.partitionFilters`]) in one pass. `p` may perform
--| abilities: it runs once per element, in list order.
def List.partition (xs: List a) (p: a → {e} Bool): {e} Pair (List a) (List a) := List.partitionOnto p xs (MkPair [] [])

test "List.partition" := List.partition [1, 5, 2, 7] (x => x > 4) == MkPair [5, 7] [1, 2] ∧ List.partition ([]: List Nat) (x => x > 4) == MkPair [] []

--| The value for the first pair whose key equals `key`, or `None` if there is none.
@[tailrec]
def List.lookup [auto eq: DecEq k]: (entries: List (Pair k v)) → (key: k) → Option v
  | [], key => None
  | [MkPair entryKey value, ..rest], key => if entryKey == key then Some value else rest.lookup key

--| `List.padRight xs n x` is `xs` followed by enough copies of `x` to make it
--| n long (it is `xs` itself when that is already n long or longer).
def List.padRight (xs: List a) (n: Nat) (x: a): List a := xs.append (List.replicate (n - xs.length) x)

--| `xs` after enough copies of `x` to make it `n` long (`xs` itself when it is already that long).
def List.padLeft (xs: List a) (n: Nat) (x: a): List a := (List.replicate (n - xs.length) x).append xs

--| `Some` of every value when every option has one, else `None`.
def List.allSome: (options: List (Option a)) → Option (List a)
  | [] => Some []
  | [first, ..rest] => first.flatMap (value => List.allSome rest |> .map (Cons value))

theorem List.allSomeExample: List.allSome [Some 1, Some 2] = Some [1, 2] := rfl

theorem List.allSomeNone: List.allSome [Some 1, None] = None := rfl

--| The first `n` columns of a list of rows (`List.transpose`'s loop): column i
--| is the i-th element of each row that has one.
@[noReceiver]
def List.transposeN: (count: Nat) → (rows: List (List a)) → List (List a)
  | Zero, rows => []
  | Succ n, rows => [List.filterMap rows (.get 0), ..List.transposeN n (List.map rows (.drop 1))]

--| Swaps rows and columns: the columns of a list of rows, as many as the first
--| row is long. For rows that are all the same length, the cell at row r and
--| column c moves to row c and column r. A row that's too short just leaves
--| its column out, and a row longer than the first loses its extra cells: the
--| result has the first row's width, so `[[1], [2, 3]].transpose` is
--| `[[1, 2]]` (Haskell's `transpose` goes to the longest row instead).
def List.transpose (rows: List (List a)): List (List a) := List.transposeN (List.length (List.headOr rows [])) rows

-- `List.All`, `List.Any` and `List.Mem` are in the core
-- (core/ListOptionPair.sw): the induction principles generated for a nested
-- type state their hypotheses with them.

--| Every row has length n (the list is rectangular).
@[noReceiver]
def List.AllLength (n: Nat): (rows: List (List a)) → Prop
  | [] => Unit
  | [r, ..rs] => (List.length r = n) ∧ (List.AllLength n rs)

--| How many elements satisfy `p` (as `List.count`, but recursing on the list,
--| which suits proofs).
def List.occurrences: (xs: List a) → (p: a → Bool) → Nat
  | [], p => 0
  | [x, ..xs], p => Bool.toNat (p x) + List.occurrences xs p

--| `xs` and `ys` are permutations of each other: every test is passed by as
--| many elements of one as of the other. For elements with decidable equality
--| this is the usual meaning (test with `Nat.equal v` for each `v`). Counting
--| turns the proofs into arithmetic, and needs no equality on the elements.
--| Permutations are as long as each other ([`List.permLength`]).
def List.Perm (xs: List a) (ys: List a): Prop := (p: a → Bool) → List.occurrences xs p = List.occurrences ys p

--| `s` is `xs` with some elements left out, the rest kept in order: each
--| element of `s` is matched with an element of `xs`, or `xs`'s first element
--| is skipped. So `s` is no longer than `xs` ([`List.subsequenceLength`]).
def List.Subsequence: (xs: List a) → (ys: List a) → Prop
  | [], ys => Unit
  | [x, ..xs], [] => Void
  | [x, ..xs], [y, ..ys] => ((x = y) ∧ (List.Subsequence xs ys)) ∨ (List.Subsequence [x, ..xs] ys)

--| Congruence lemmas: given callbacks that agree on every argument, a function
--| gives the same result. Their shape is fixed, since `decreasing` looks them up
--| by name (`F` + `Cong`) to follow a recursive call inside a callback:
--| `F`'s parameters in order, each callback twice, then `(x…) -> f1 x… = f2 x…`
--| for each.
-- (docs/proposals/well-founded-recursion.md, stage 3a)
theorem List.mapCong: (xs: List a) → (f1: a → b) → (f2: a → b) → ((x: a) → f1 x = f2 x) → List.map xs f1 = List.map xs f2
  | [], f1, f2, ef => rfl
  | [x, ..xs], f1, f2, ef => Eq.trans (Eq.cong (y => [y, ..List.map xs f1]) (ef x)) (Eq.cong (ys => [f2 x, ..ys]) (List.mapCong xs f1 f2 ef))

theorem List.filterMapCong: (xs: List a) → (f1: a → Option b) → (f2: a → Option b) → ((x: a) → f1 x = f2 x) → List.filterMap xs f1 = List.filterMap xs f2
  | [], f1, f2, ef => rfl
  | [x, ..xs], f1, f2, ef => rewrite ef x, List.filterMapCong xs f1 f2 ef

theorem List.findCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.find xs p1 = List.find xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x, List.findCong xs p1 p2 ep

theorem List.anyCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.any xs p1 = List.any xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x, List.anyCong xs p1 p2 ep

theorem List.allCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) → List.all xs p1 = List.all xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x, List.allCong xs p1 p2 ep

theorem List.occurrencesCong: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → p1 x = p2 x) →
    List.occurrences xs p1 = List.occurrences xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep =>
    Eq.trans (Eq.cong (b => Bool.toNat b + List.occurrences xs p1) (ep x))
      (Eq.cong (n => Bool.toNat (p2 x) + n) (List.occurrencesCong xs p1 p2 ep))

theorem List.foldLeftCong: (xs: List a) → (z: b) → (f1: b → a → b) → (f2: b → a → b) → ((acc: b) → (x: a) → f1 acc x = f2 acc x) →
    List.foldLeft xs z f1 = List.foldLeft xs z f2
  | [], z, f1, f2, ef => rfl
  | [x, ..xs], z, f1, f2, ef => Eq.trans (Eq.cong (t => List.foldLeft xs t f1) (ef z x)) (List.foldLeftCong xs (f2 z x) f1 f2 ef)

theorem List.sumByCong [auto add: Add b] (xs: List a) (f1: a → b) (f2: a → b) (ef: (x: a) → f1 x = f2 x): List.sumBy xs f1 = List.sumBy xs f2 :=
  List.foldLeftCong xs Add.zero (acc x => acc + f1 x) (acc x => acc + f2 x) (acc x => Eq.cong (t => acc + t) (ef x))

--| Decides `x ∈ xs` one element at a time from the front, so `x ∈ xs` is a
--| `Bool` where one is expected (`if x ∈ seen`) and `if h: x ∈ xs` names
--| the proof.
-- Its type spells out `List.Mem`: `∈` there would make the type mention the
-- instance itself.
instance List.decMem [auto eq: DecEq a] (x: a): (xs: List a) → Decidable (List.Mem x xs)
  | [] => No (none => none)
  | [y, ..ys] => Decidable.or (eq.decide y x) (List.decMem x ys)

test "List.decMem" := 2 ∈ [1, 2, 3] ∧ 4 ∉ [1, 2, 3] ∧ 'a' ∉ []

test "List.decMem on a variable" := List.all [3, 1] (x => x ∈ [1, 2, 3])

--| No element of the first list is in the second.
def List.Disjoint (xs: List a) (ys: List a): Prop := List.All (x => x ∉ ys) xs

--| No element occurs twice.
def List.Distinct: (xs: List a) → Prop
  | [] => Unit
  | [x, ..xs] => (x ∉ xs) ∧ (List.Distinct xs)

--| Decides `List.Distinct xs` by checking each element against those after
--| it (quadratic; `List.allDistinct` is the faster test, given an `Ord`).
-- Its type spells out `List.Distinct`, as `List.decMem`'s does.
instance List.decDistinct [auto eq: DecEq a]: (xs: List a) → Decidable (List.Distinct xs)
  | [] => Yes Trivial
  | [x, ..xs] => Decidable.and (Decidable.not (List.decMem x xs)) (List.decDistinct xs)

test "List.decDistinct" := List.Distinct [1, 2, 3] ∧ ¬(List.Distinct [1, 2, 1]) ∧ List.Distinct ([]: List Nat)

--| The run `List.rangeFrom c s` holds the numbers from `s` up to, not
--| including, `s + c`.
theorem List.memRangeFrom (x: Nat): (c: Nat) → (s: Nat) → x ∈ List.rangeFrom c s → (s ≤ x) ∧ (x < s + c)
  | Zero, s, h => Void.exfalso h
  | Succ c, s, Inl q => rewrite <- q in Both (Nat.leRefl s) (Nat.ltAddSuccSelf s c)
  | Succ c, s, Inr m =>
    match List.memRangeFrom x c (Succ s) m with
      | Both lo hi => Both (Nat.lessLe s x lo) (Nat.ltAddSucc s c x hi)

--| Mapping with a state threaded left to right (Haskell's `mapAccumL`).
--| `xs` is the main value: `xs.mapAccumLeft 0 (s x => MkPair (s + x) (s * x))`.
--| The function takes the state and an element and gives the next state and the
--| mapped element; the result is the final state and the mapped list.
--| A loop: `done` holds the mapped elements so far, newest first.
@[noReceiver]
@[tailrec]
def List.mapAccumLeftGo (f: s → a → Pair s b) (state: s) (done: List b): (xs: List a) → Pair s (List b)
  | [] => MkPair state (List.reverseOnto done [])
  | [x, ..xs] =>
    let next := f state x
    List.mapAccumLeftGo f (Pair.fst next) [Pair.snd next, ..done] xs

--| Maps with a state threaded left to right (Haskell's `mapAccumL`): the final state and the results.
def List.mapAccumLeft (xs: List a) (initial: s) (f: s → a → Pair s b): Pair s (List b) := List.mapAccumLeftGo f initial [] xs

--| Splits a list of pairs into the list of firsts and the list of seconds.
def List.unzip (ps: List (Pair a b)): Pair (List a) (List b) := MkPair (List.map ps Pair.fst) (List.map ps Pair.snd)

--| Dropping elements never makes a list longer.
theorem List.lengthDropLe: (xs: List a) → (n: Nat) → List.length (List.drop xs n) ≤ List.length xs
  | xs, Zero => Nat.leRefl (List.length xs)
  | [], Succ n => rfl
  | [x, ..xs], Succ n => Nat.leTrans (List.length (List.drop xs n)) (List.length xs) (Succ (List.length xs)) (List.lengthDropLe xs n) (Nat.leSucc (List.length xs))

--| Dropping at least one element of a non-empty list leaves a shorter list.
theorem List.dropConsLess: (xs: List a) → (n: Nat) → (x: a) → n ≠ 0 → List.length (List.drop [x, ..xs] n) < List.length [x, ..xs]
  | xs, Zero, x, h => Void.exfalso (h rfl)
  | xs, Succ n, x, h => Nat.leLessSucc (List.length (List.drop xs n)) (List.length xs) (List.lengthDropLe xs n)

--| Chunks of `n` elements, in order; the last chunk is shorter when `n` doesn't
--| divide the length. `n = 0` is no sensible chunk size, so it gives the whole
--| list as one chunk (`[xs]`, or `[]` for an empty `xs`).
@[noReceiver]
def List.chunksOfPositive (n: Nat) (xs: List a) [auto pos: n ≠ 0]: List (List a)
    decreasing List.length xs
:=
  match xs with
    | [] => []
    | [y, ..ys] => [List.take [y, ..ys] n, ..List.chunksOfPositive n (List.drop [y, ..ys] n) [decreasing := List.dropConsLess ys n y pos]]

--| Chunks of `n` elements, in order, the last one shorter if need be:
--| `[1, 2, 3].chunksOf 2` is `[[1, 2], [3]]`. `n = 0` gives the whole list as
--| one chunk (none for an empty list).
def List.chunksOf (xs: List a) (n: Nat): List (List a) :=
  match n with
    | Zero => match xs with
      | [] => []
      | [y, ..ys] => [[y, ..ys]]
    | Succ k => List.chunksOfPositive (Succ k) xs

--| The elements without repeats, keeping the first occurrence of each and the
--| order. `seen` is what came before. Needs only `DecEq`, so it is quadratic:
--| each element is compared with every one kept before it.
@[noReceiver]
def List.distinctFrom [auto eq: DecEq a] (seen: List a): (xs: List a) → List a
  | [] => []
  | [x, ..xs] => if List.any seen (== x) then List.distinctFrom seen xs else [x, ..List.distinctFrom [x, ..seen] xs]

--| `List.distinct` for a type with `==` but no ordering: the same result,
--| quadratic. `[3, 1, 3, 2, 1].distinctEq` is `[3, 1, 2]`. With an ordering,
--| use `List.distinct` (std/List/Distinct.sw, with the theorems about both),
--| O(n log n).
def List.distinctEq [auto eq: DecEq a] (xs: List a): List a := List.distinctFrom [] xs

test "List.mapAccumLeft" := [1, 2, 3].mapAccumLeft 0 (s x => MkPair (s + x) (s * x)) == MkPair 6 [0, 2, 9]
test "List.mapAccumLeft empty" := ([]: List Nat).mapAccumLeft 7 (s x => MkPair (s + x) x) == MkPair 7 []
test "List.unzip" := List.unzip [MkPair 1 True, MkPair 2 False] == MkPair [1, 2] [True, False]
test "List.unzip empty" := List.unzip ([]: List (Pair Nat Nat)) == MkPair [] []
test "List.chunksOf" := List.chunksOf [1, 2, 3, 4, 5] 2 == [[1, 2], [3, 4], [5]]
test "List.chunksOf exact" := List.chunksOf [1, 2, 3, 4] 2 == [[1, 2], [3, 4]]
test "List.chunksOf bigger than the list" := List.chunksOf [1, 2] 5 == [[1, 2]]
test "List.chunksOf empty" := List.chunksOf ([]: List Nat) 3 == []
test "List.chunksOf zero is one chunk" := List.chunksOf [1, 2, 3] 0 == [[1, 2, 3]] ∧ List.chunksOf ([]: List Nat) 0 == []
test "List.distinctEq" := [3, 1, 3, 2, 1].distinctEq == [3, 1, 2]
test "List.distinctEq empty" := ([]: List Nat).distinctEq == []
test "List.distinctEq all repeats" := [4, 4, 4].distinctEq == [4]
test "List.distinctEq already distinct" := [2, 5, 1].distinctEq == [2, 5, 1]

--| One step of `List.maxBy`: `x` if its key is larger than `best`'s, otherwise `best`.
def List.maxByStep [auto ord: Ord b] (f: a → b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Less => x
  | _ => best

--| The element with the largest key, or `None` for an empty list. When several
--| keys are largest, the FIRST of those elements wins:
--| `[(1, "a"), (3, "b"), (3, "c")].maxBy Pair.fst` is `Some (3, "b")`.
--| (Haskell's `maximumBy` and Clojure's `max-key` return the last one, so a
--| port must not assume they agree.)
def List.maxBy [auto ord: Ord b] (xs: List a) (f: a → b): Option a :=
  match xs with
    | [] => None
    | [x, ..ys] => Some (List.foldLeft ys x (best y => List.maxByStep f best y))

--| One step of `List.minBy`: `x` if its key is smaller than `best`'s, otherwise `best`.
def List.minByStep [auto ord: Ord b] (f: a → b) (best: a) (x: a): a := match Ord.compare (f best) (f x) with
  | Greater => x
  | _ => best

--| The element with the smallest key; on a tie the FIRST one wins, as for
--| `List.maxBy`.
def List.minBy [auto ord: Ord b] (xs: List a) (f: a → b): Option a :=
  match xs with
    | [] => None
    | [x, ..ys] => Some (List.foldLeft ys x (best y => List.minByStep f best y))

--| The largest value of `f` over the elements, or `None` for an empty list:
--| `[(1, "a"), (3, "b"), (2, "c")].maximumOf Pair.fst` is `Some 3`. Where
--| `List.maxBy` returns the element whose key is largest, this returns the
--| key itself; it is `(xs.map f).maximum` ([`List.maximumOfMap`]), so the
--| `List.maximum` lemmas apply to it.
def List.maximumOf [auto ord: Ord b] (xs: List a) (f: a → b): Option b := List.maximum (List.map xs f)

theorem List.maximumOfMap [auto ord: Ord b] (xs: List a) (f: a → b): List.maximumOf xs f = List.maximum (List.map xs f) := rfl

--| The smallest value of `f` over the elements, or `None` for an empty list:
--| `[(1, "a"), (3, "b"), (2, "c")].minimumOf Pair.fst` is `Some 1`. Where
--| `List.minBy` returns the element whose key is smallest, this returns the
--| key itself; it is `(xs.map f).minimum` ([`List.minimumOfMap`]), so the
--| `List.minimum` lemmas apply to it.
def List.minimumOf [auto ord: Ord b] (xs: List a) (f: a → b): Option b := List.minimum (List.map xs f)

theorem List.minimumOfMap [auto ord: Ord b] (xs: List a) (f: a → b): List.minimumOf xs f = List.minimum (List.map xs f) := rfl

--| The longest prefix of elements satisfying `p`. `p` may perform abilities:
--| it runs in list order and isn't called after the first element that fails
--| it.
def List.takeWhile (xs: List a) (p: a → {e} Bool): {e} List a :=
  match xs with
    | [] => []
    | [x, ..ys] => if p x then [x, ..List.takeWhile ys p] else []

--| What is left after `List.takeWhile`: from the first element not satisfying `p`
--| ([`List.takeWhileDropWhile`]).
@[tailrec]
def List.dropWhile (xs: List a) (p: a → Bool): List a :=
  match xs with
    | [] => []
    | [x, ..ys] => if p x then List.dropWhile ys p else [x, ..ys]

--| `List.span`'s loop: `taken` is the prefix so far, reversed.
@[noReceiver]
@[tailrec]
def List.spanOnto (taken: List a) (p: a → {e} Bool): (xs: List a) → {e} Pair (List a) (List a)
  | [] => MkPair (List.reverse taken) []
  | [x, ..xs] => if p x then List.spanOnto [x, ..taken] p xs else MkPair (List.reverse taken) [x, ..xs]

--| `List.takeWhile` and `List.dropWhile` together ([`List.spanTakeDrop`]), in
--| one pass. `p` may perform abilities: it runs in list order and isn't
--| called after the first element that fails it.
def List.span (xs: List a) (p: a → {e} Bool): {e} Pair (List a) (List a) := List.spanOnto [] p xs

--| The first `n` elements and the rest: `xs.splitAt 2` is `(xs.take 2, xs.drop 2)`.
def List.splitAt (xs: List a) (n: Nat): Pair (List a) (List a) := MkPair (List.take xs n) (List.drop xs n)

--| Without the element at `index`, counting from 0 (the same list if there is
--| none): `[1, 2, 3].removeAt 1` is `[1, 3]`.
def List.removeAt: (xs: List a) → (index: Nat) → List a
  | [], index => []
  | [x, ..xs], Zero => xs
  | [x, ..xs], Succ index => [x, ..List.removeAt xs index]

--| Without the last `n` elements (all of them if there are fewer).
def List.dropRight (xs: List a) (n: Nat): List a := List.take xs (List.length xs - n)

--| Every suffix, longest first, ending with the empty list:
--| `[1, 2].tails` is `[[1, 2], [2], []]`: one more than the elements ([`List.lengthTails`]).
def List.tails: (xs: List a) → List (List a)
  | [] => [[]]
  | [x, ..xs] => [[x, ..xs], ..List.tails xs]

--| Every run of `size` consecutive elements, in order (sliding windows):
--| `[1, 2, 3, 4].windows 3` is `[[1, 2, 3], [2, 3, 4]]`. A list of length n
--| has n + 1 - size of them: none when it is shorter than `size`, and for
--| `size = 0`, n + 1 empty windows (one before each element and one at the
--| end). Lemmas: [`List.lengthWindows`], [`List.lengthOfMemWindows`],
--| [`List.windowsCons`], [`List.windowsShort`], [`List.windowsTails`].
def List.windows (xs: List a) (size: Nat): List (List a) := List.windowsCount size (List.length xs + 1 - size) xs

--| The first `count` windows of `size` elements of `xs`, one step apart.
@[noReceiver]
def List.windowsCount (size: Nat): (count: Nat) → (xs: List a) → List (List a)
  | Zero, xs => []
  | Succ count, xs => [List.take xs size, ..List.windowsCount size count (List.drop xs 1)]

test "List.windows" :=
  [1, 2, 3, 4].windows 3 == [[1, 2, 3], [2, 3, 4]] ∧ [1, 2].windows 3 == [] ∧ [1, 2].windows 2 == [[1, 2]]
    ∧ [1, 2].windows 0 == [[], [], []] ∧ ([]: List Nat).windows 1 == []

--| The index of the first element satisfying `p`, counting from `i`.
@[noReceiver]
@[tailrec]
def List.findIndexFrom (i: Nat) (p: a → Bool): (xs: List a) → Option Nat
  | [] => None
  | [x, ..xs] => if p x then Some i else List.findIndexFrom (Succ i) p xs

--| The index of the first element satisfying `p`, counting from 0, or `None` if none does.
def List.findIndex (xs: List a) (p: a → Bool): Option Nat := List.findIndexFrom 0 p xs

--| Each element with its index from `i`.
@[noReceiver]
def List.withIndexFrom (i: Nat): (xs: List a) → List (Pair Nat a)
  | [] => []
  | [x, ..xs] => [MkPair i x, ..List.withIndexFrom (Succ i) xs]

--| Pairs each element with its position, counting from 0, the position first:
--| `["a", "b"].withIndex` is `[(0, "a"), (1, "b")]`. Rust's `enumerate`
--| ([`List.withIndexRange`]).
def List.withIndex (xs: List a): List (Pair Nat a) := List.withIndexFrom 0 xs

--| `f` of each element's index and the element:
--| `["a", "b"].mapWithIndex (index x => "${index}${x}")` is `["0a", "1b"]`.
def List.mapWithIndex (xs: List a) (f: Nat → a → {e} b): {e} List b := xs.withIndex.map (pair => f pair.fst pair.snd)

--| One step of `List.findMap`: the `Some` found, or else the search of the
--| rest, which runs only then. The rest is a function of no arguments so that
--| an effectful `f` isn't called after the first `Some`.
-- A function of its own (not a `match` in `findMap`) so the backends inline
-- it and `findMap` stays a loop.
@[noReceiver]
def List.findMapStep: (first: Option b) → (rest: () → {e} Option b) → {e} Option b
  | Some y, rest => Some y
  | None, rest => rest ()

--| The first `Some` that `f` gives (Lean's `findSome?`, Scala's `collectFirst`):
--| `lines.findMap (match some | Header title => title)` is the first header's title.
--| `f` may perform abilities: it runs in list order and isn't called after the
--| first `Some`.
def List.findMap (xs: List a) (f: a → {e} Option b): {e} Option b :=
  match xs with
    | [] => None
    | [x, ..ys] => List.findMapStep (f x) (() => List.findMap ys f)

--| Maps, then joins: `xs.flatMap f` is `List.concat (List.map xs f)`. `f` may
--| perform abilities, which run in list order. Its length is the sum of the
--| lengths ([`List.lengthFlatMap`]).
def List.flatMap (xs: List a) (f: a → {e} List b): {e} List b := List.concat (List.map xs f)

theorem List.flatMapCong (xs: List a) (f1: a → List b) (f2: a → List b) (ef: (x: a) → f1 x = f2 x): List.flatMap xs f1 = List.flatMap xs f2 :=
  Eq.cong List.concat (List.mapCong xs f1 f2 ef)

--| Every pair, the first elements in order and the second elements within each:
--| `[1, 2].cross ["a", "b"]` is `[(1, "a"), (1, "b"), (2, "a"), (2, "b")]`.
def List.cross (xs: List a) (ys: List b): List (Pair a b) := List.flatMap xs (x => List.map ys (y => MkPair x y))

--| Every element with each later one, in order: `[1, 2, 3].pairs` is
--| `[(1, 2), (1, 3), (2, 3)]`. A list of n elements has n(n - 1)/2 of them
--| ([`List.lengthPairs`]).
def List.pairs: (xs: List a) → List (Pair a a)
  | [] => []
  | [x, ..xs] => List.append (List.map xs (y => MkPair x y)) (List.pairs xs)

test "List.maxBy" := [MkPair 2 "bb", MkPair 1 "a", MkPair 3 "ccc"].maxBy Pair.fst == Some (MkPair 3 "ccc") ∧ ([]: List Nat).maxBy (x => x) == None
test "List.maxBy first wins a tie" := [MkPair 1 "a", MkPair 3 "b", MkPair 3 "c"].maxBy Pair.fst == Some (MkPair 3 "b")
test "List.minBy first wins a tie" := [MkPair 3 "z", MkPair 1 "a", MkPair 1 "b"].minBy Pair.fst == Some (MkPair 1 "a") ∧ ([]: List Nat).minBy (x => x) == None
test "List.maximumOf" := [2, 9, 4].maximumOf (n => n % 5) == Some 4 ∧ ([]: List Nat).maximumOf (n => n) == None
test "List.minimumOf" := [7, 9, 4].minimumOf (n => n % 5) == Some 2 ∧ ([]: List Nat).minimumOf (n => n) == None
test "List.maximumOf gives the key, not the element" := [MkPair 1 "a", MkPair 3 "b", MkPair 2 "c"].maximumOf Pair.fst == Some 3
test "List.takeWhile and dropWhile" := [1, 2, 5, 1].takeWhile (x => Nat.leq x 2) == [1, 2] ∧ [1, 2, 5, 1].dropWhile (x => Nat.leq x 2) == [5, 1]
test "List.takeWhile all and none" := [1, 2].takeWhile (x => Nat.leq x 8) == [1, 2] ∧ [1, 2].dropWhile (x => Nat.leq x 8) == [] ∧ [4].takeWhile (x => Nat.leq x 2) == []
test "List.span" := List.span [1, 2, 5, 1] (x => Nat.leq x 2) == MkPair [1, 2] [5, 1] ∧ List.span ([]: List Nat) (x => Nat.leq x 2) == MkPair [] []
test "List.span dot" := [1, 2, 5, 1].span (x => Nat.leq x 2) == MkPair [1, 2] [5, 1]
test "List.splitAt" := [1, 2, 3].splitAt 1 == MkPair [1] [2, 3] ∧ [1, 2].splitAt 5 == MkPair [1, 2] [] ∧ [1, 2].splitAt 0 == MkPair [] [1, 2]
test "List.dropRight" := [1, 2, 3, 4].dropRight 1 == [1, 2, 3] ∧ [1, 2].dropRight 5 == [] ∧ [1, 2].dropRight 0 == [1, 2]
test "List.tails" := [1, 2].tails == [[1, 2], [2], []] ∧ ([]: List Nat).tails == [[]]
test "List.findIndex" := [5, 6, 7].findIndex (x => Nat.leq 6 x) == Some 1 ∧ [5].findIndex (x => Nat.leq 10 x) == None
test "List.withIndex" := ["a", "b"].withIndex == [MkPair 0 "a", MkPair 1 "b"] ∧ ([]: List Nat).withIndex == []
test "List.mapWithIndex" := ["a", "b"].mapWithIndex (index x => "${index}${x}") == ["0a", "1b"] ∧ ([]: List Nat).mapWithIndex (index x => index + x) == []
test "List.mapWithIndex is withIndex then map" := [5, 6, 7].mapWithIndex (index x => index * x) == [5, 6, 7].withIndex.map (((index, x)) => index * x)
test "List.findMap" := [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == Some 30 ∧ [1].findMap (x => (None: Option Nat)) == None
test "List.findMap is the head of filterMap" :=
  [1, 2, 3, 4].findMap (x => if Nat.leq 3 x then Some (x * 10) else None) == ([1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 10) else None)).head ∧
    [1].findMap (x => (None: Option Nat)) == ([1].filterMap (x => (None: Option Nat))).head
test "List.between" := List.between 2 5 == [2, 3, 4, 5] ∧ List.between 3 3 == [3] ∧ List.between 4 2 == [] ∧ List.between 0 1 == [0, 1]
test "List.flatMap" := [1, 2, 3].flatMap (x => List.replicate x x) == [1, 2, 2, 3, 3, 3]
test "List.contains" := [1, 2, 3].contains 2 ∧ ¬([1, 2, 3].contains 4) ∧ ¬(([]: List Nat).contains 1)
test "List.pairs" := [1, 2, 3].pairs == [MkPair 1 2, MkPair 1 3, MkPair 2 3] ∧ ([]: List Nat).pairs == [] ∧ [1].pairs == ([]: List (Pair Nat Nat))
test "List.pairs count" := List.length (List.range 10).pairs == 45

--| Every choice of `k` elements, in the order they come: `[1, 2, 3, 4].combinations 3`
--| is `[[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]]`. Like [`List.pairs`], it
--| chooses by position: equal elements at different places are different
--| choices. `xs.combinations 2` is `xs.pairs` as lists of two, and
--| `xs.combinations 0` is `[[]]`. A choice is a subsequence of `xs` of length
--| `k`, and every such subsequence is a choice ([`List.memCombinations`],
--| [`List.combinationsMem`]).
def List.combinations: (xs: List a) → (size: Nat) → List (List a)
  | xs, Zero => [[]]
  | [], Succ k => []
  | [x, ..xs], Succ k => List.append (List.map (List.combinations xs k) (ys => [x, ..ys])) (List.combinations xs (Succ k))

test "List.combinations" := [1, 2, 3, 4].combinations 3 == [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]]
test "List.combinations of one and all" := [1, 2, 3].combinations 1 == [[1], [2], [3]] ∧ [1, 2, 3].combinations 3 == [[1, 2, 3]]
test "List.combinations of none, and more than there are" := [1, 2, 3].combinations 0 == [[]] ∧ ([]: List Nat).combinations 0 == [[]] ∧ [1, 2].combinations 3 == [] ∧ ([]: List Nat).combinations 1 == []
test "List.combinations chooses by position" := [7, 7, 7].combinations 2 == [[7, 7], [7, 7], [7, 7]]
test "List.combinations 2 agrees with pairs" := [1, 2, 3, 4].combinations 2 == [1, 2, 3, 4].pairs.map (p => [p.fst, p.snd])
test "List.combinations count" := List.length ((List.range 10).combinations 4) == 210
test "List.cross" := [1, 2].cross ["a", "b"] == [MkPair 1 "a", MkPair 1 "b", MkPair 2 "a", MkPair 2 "b"] ∧ [1].cross ([]: List Nat) == []

--| Callbacks that agree on the list's elements (not everywhere, as for
--| [`List.mapCong`]) give the same result.
theorem List.mapCongMem: (xs: List a) → (f1: a → b) → (f2: a → b) → ((x: a) → (m: x ∈ xs) → f1 x = f2 x) → List.map xs f1 = List.map xs f2
  | [], f1, f2, ef => rfl
  | [x, ..xs], f1, f2, ef => rewrite ef x (Inl rfl), List.mapCongMem xs f1 f2 (y m => ef y (Inr m))

theorem List.filterCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.filter xs p1 = List.filter xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x (Inl rfl), List.filterCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.anyCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.any xs p1 = List.any xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x (Inl rfl), List.anyCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.allCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) → List.all xs p1 = List.all xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x (Inl rfl), List.allCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.occurrencesCongMem: (xs: List a) → (p1: a → Bool) → (p2: a → Bool) → ((x: a) → (m: x ∈ xs) → p1 x = p2 x) →
    List.occurrences xs p1 = List.occurrences xs p2
  | [], p1, p2, ep => rfl
  | [x, ..xs], p1, p2, ep => rewrite ep x (Inl rfl), List.occurrencesCongMem xs p1 p2 (y m => ep y (Inr m))

theorem List.foldLeftCongMem: (xs: List a) → (z: b) → (f1: b → a → b) → (f2: b → a → b) → ((acc: b) → (x: a) → (m: x ∈ xs) → f1 acc x = f2 acc x) →
    List.foldLeft xs z f1 = List.foldLeft xs z f2
  | [], z, f1, f2, ef => rfl
  | [x, ..xs], z, f1, f2, ef =>
    Eq.trans (Eq.cong (t => List.foldLeft xs t f1) (ef z x (Inl rfl))) (List.foldLeftCongMem xs (f2 z x) f1 f2 (acc y m => ef acc y (Inr m)))

theorem List.filterMapCongMem: (xs: List a) → (f1: a → Option b) → (f2: a → Option b) → ((x: a) → (m: x ∈ xs) → f1 x = f2 x) →
    List.filterMap xs f1 = List.filterMap xs f2
  | [], f1, f2, ef => rfl
  | [x, ..xs], f1, f2, ef => rewrite ef x (Inl rfl), List.filterMapCongMem xs f1 f2 (y m => ef y (Inr m))

--| Over a run of numbers, the facts are the run's bounds. `rewrite` tries a
--| function's `…CongRange` lemma first, then `…CongMem`, then `…Cong`, and
--| rewriting inside the function has the facts as hypotheses.
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

--| `sumBy` and `count` are folds, so their congruence lemmas are the fold's.
theorem List.sumByCongRange [auto add: Add c] (f: Nat → c) (g: Nat → c): (c: Nat) → (s: Nat) → ((x: Nat) → s ≤ x → x < s + c → f x = g x) →
    List.sumBy (List.rangeFrom c s) f = List.sumBy (List.rangeFrom c s) g :=
  c s h => List.foldLeftCongRange (acc x => acc + f x) (acc x => acc + g x) Add.zero c s (acc x low high => Eq.cong (t => acc + t) (h x low high))

--| Sums agree when their terms agree on the list's elements.
theorem List.sumByCongMem [auto add: Add b] (xs: List a) (f: a → b) (g: a → b) (agree: (x: a) → x ∈ xs → f x = g x):
    List.sumBy xs f = List.sumBy xs g :=
  List.foldLeftCongMem xs Add.zero (acc x => acc + f x) (acc x => acc + g x) (acc x m => Eq.cong (t => acc + t) (agree x m))

theorem List.countCongMem (xs: List a) (p1: a → Bool) (p2: a → Bool) (ep: (x: a) → (m: List.Mem x xs) → p1 x = p2 x): List.count xs p1 = List.count xs p2 :=
  List.foldLeftCongMem xs 0 (n x => Nat.succIf n (p1 x)) (n x => Nat.succIf n (p2 x)) (acc x m => Eq.cong (b => Nat.succIf acc b) (ep x m))
