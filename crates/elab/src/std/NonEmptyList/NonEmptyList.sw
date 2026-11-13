--| `NonEmptyList a`: a list with at least one element, as a first element
--| and the rest, `{ head = 1, tail = [2, 3] }`. Where `List` returns an
--| `Option` (`List.maximum`, `List.last`, …) the `NonEmptyList` function
--| returns the value, and the ones that keep a list non-empty (`map`, `zip`,
--| `sort`, `reverse`, `append`) return a `NonEmptyList` again.
--|
--| Each function has the name of its `List` twin, and a lemma saying it is
--| that twin on `toList` (`NonEmptyList.maximumToList`: `xs.toList.maximum` is
--| `Some xs.maximum`), so the `List` lemmas apply through `toList`. `toList`
--| is `[xs.head, ..xs.tail]`, a `Cons` for every `xs`, which is why most of
--| those lemmas are `rfl`. There are no coercions: `xs.toList` goes back to a
--| `List`, and `ys.toNonEmpty` (given a proof that `ys ≠ []`, found by `auto`)
--| or `ys.nonEmpty` (an `Option`) goes forward.
--|
--| `++` is `List`'s and `Text`'s only, so the joins are `append` (two
--| `NonEmptyList`s), `appendList` and `prependList`.
-- docs/proposals/non-empty-lists.md

import Std (Eq)

--| A list with at least one element: the first, then the rest.
type NonEmptyList (a: Type) = { head: a, tail: List a }

--| The list of one element.
def NonEmptyList.singleton (x: a): NonEmptyList a := { head = x, tail = [] }

--| `x` in front of a list: `NonEmptyList.cons 1 [2, 3]` is `{ head = 1, tail = [2, 3] }`.
@[noReceiver]
def NonEmptyList.cons (x: a) (rest: List a): NonEmptyList a := { head = x, tail = rest }

--| The elements as a plain `List`: `[xs.head, ..xs.tail]`. It is never empty ([`NonEmptyList.toListNotNil`]).
def NonEmptyList.toList (xs: NonEmptyList a): List a := [xs.head, ..xs.tail]

--| The list as a `NonEmptyList`, where it is known not to be empty: `auto` finds
--| the proof for a literal, in the `[x, ..rest]` arm of a match and after
--| `if h: xs ≠ [] then`. The result is the list again ([`List.toNonEmptyToList`]).
def List.toNonEmpty (xs: List a) [auto nonEmpty: xs ≠ []]: NonEmptyList a := match xs with
  | [] => Void.absurd (nonEmpty rfl)
  | [x, ..rest] => { head = x, tail = rest }

--| The list as a `NonEmptyList`, or `None` for an empty list
--| ([`List.nonEmptyNil`], [`List.nonEmptyCons`]). It keeps the list's own head
--| and tail; to keep a proof that the list isn't empty, use [`List.toNonEmpty`].
def List.nonEmpty: (xs: List a) → Option (NonEmptyList a)
  | [] => None
  | [x, ..rest] => Some { head = x, tail = rest }

--| The number of elements, at least one ([`NonEmptyList.lengthPos`]): the length of `toList` ([`NonEmptyList.lengthToList`]).
def NonEmptyList.length (xs: NonEmptyList a): Nat := Succ (List.length xs.tail)

--| How many elements satisfy `p`, at most the length; `p` may perform
--| abilities, which run in list order ([`NonEmptyList.countToList`]).
def NonEmptyList.count (xs: NonEmptyList a) (p: a → {e} Bool): {e} Nat := List.count xs.toList p

--| The sum of `f` over the elements ([`NonEmptyList.sumByToList`]). `f` may
--| perform abilities, which run in list order.
def NonEmptyList.sumBy [auto add: Add b] (xs: NonEmptyList a) (f: a → {e} b): {e} b := List.sumBy xs.toList f

--| Left fold: `xs.foldLeft z f` is `xs.toList.foldLeft z f`. `f` may perform abilities, which run in list order.
def NonEmptyList.foldLeft (xs: NonEmptyList a) (initial: b) (f: b → a → {e} b): {e} b := List.foldLeft xs.toList initial f

--| Right fold: `xs.foldRight z f` is `xs.toList.foldRight z f`.
def NonEmptyList.foldRight (xs: NonEmptyList a) (initial: b) (f: a → b → {e} b): {e} b := List.foldRight xs.toList initial f

--| Combines the elements left to right, starting from the first: `[x, y, z].reduce f` is
--| `f (f x y) z`. Where `List` has no first element to start from and
--| `foldLeft` needs a made-up one, this is total: `people.map .answers |> .reduce Set.intersect`.
def NonEmptyList.reduce (xs: NonEmptyList a) (f: a → a → {e} a): {e} a := List.foldLeft xs.tail xs.head f

--| The last element ([`NonEmptyList.lastToList`]).
def NonEmptyList.last (xs: NonEmptyList a): a := NonEmptyList.lastFrom xs.head xs.tail

--| The last of `x` followed by `rest`.
@[noReceiver]
def NonEmptyList.lastFrom (x: a): (xs: List a) → a
  | [] => x
  | [y, ..ys] => NonEmptyList.lastFrom y ys

--| All but the last element (empty for one element).
def NonEmptyList.init (xs: NonEmptyList a): List a := List.init xs.toList

--| The element at `index`, counting from 0, or `None` past the end
--| ([`NonEmptyList.getToList`]).
def NonEmptyList.get (xs: NonEmptyList a) (index: Nat): Option a := List.get xs.toList index

--| The element at `index`, or `fallback` past the end ([`NonEmptyList.getOrToList`]).
def NonEmptyList.getOr (xs: NonEmptyList a) (index: Nat) (fallback: a): a := List.getOr xs.toList index fallback

--| The largest element by the type's `Ord`: `Some xs.maximum` is `xs.toList.maximum` ([`NonEmptyList.maximumToList`]).
def NonEmptyList.maximum [auto ord: Ord a] (xs: NonEmptyList a): a := List.foldLeft xs.tail xs.head Ord.max

--| The smallest element by the type's `Ord`: `Some xs.minimum` is `xs.toList.minimum` ([`NonEmptyList.minimumToList`]).
def NonEmptyList.minimum [auto ord: Ord a] (xs: NonEmptyList a): a := List.foldLeft xs.tail xs.head Ord.min

--| The element with the largest key; on a tie the FIRST one wins, as for
--| `List.maxBy` ([`NonEmptyList.maxByToList`]).
def NonEmptyList.maxBy [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): a :=
  List.foldLeft xs.tail xs.head (best y => List.maxByStep f best y)

--| The element with the smallest key; on a tie the FIRST one wins, as for
--| `List.minBy` ([`NonEmptyList.minByToList`]).
def NonEmptyList.minBy [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): a :=
  List.foldLeft xs.tail xs.head (best y => List.minByStep f best y)

--| The largest value of `f` over the elements ([`NonEmptyList.maximumOfToList`]).
def NonEmptyList.maximumOf [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): b := NonEmptyList.maximum (NonEmptyList.map xs f)

--| The smallest value of `f` over the elements ([`NonEmptyList.minimumOfToList`]).
def NonEmptyList.minimumOf [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): b := NonEmptyList.minimum (NonEmptyList.map xs f)

--| `f` on every element, in order; `f` may perform abilities ([`NonEmptyList.mapToList`]).
def NonEmptyList.map (xs: NonEmptyList a) (f: a → {e} b): {e} NonEmptyList b :=
  let first := f xs.head
  { head = first, tail = List.map xs.tail f }

--| `f` on every element, joined ([`NonEmptyList.flatMapToList`]). `f` may
--| perform abilities, which run in list order.
def NonEmptyList.flatMap (xs: NonEmptyList a) (f: a → {e} List b): {e} List b := List.flatMap xs.toList f

--| The elements of two lists paired up, up to the shorter one's length ([`NonEmptyList.zipToList`]).
def NonEmptyList.zip (xs: NonEmptyList a) (ys: NonEmptyList b): NonEmptyList (Pair a b) :=
  { head = MkPair xs.head ys.head, tail = List.zip xs.tail ys.tail }

--| The elements of two lists combined with `f`, up to the shorter one's length ([`NonEmptyList.zipWithToList`]).
def NonEmptyList.zipWith (xs: NonEmptyList a) (ys: NonEmptyList b) (f: a → b → c): NonEmptyList c :=
  { head = f xs.head ys.head, tail = List.zipWith xs.tail ys.tail f }

--| Adds the elements of `acc` to `rest`, last first, for [`NonEmptyList.reverse`].
@[noReceiver]
def NonEmptyList.reverseOnto (acc: NonEmptyList a): (xs: List a) → NonEmptyList a
  | [] => acc
  | [y, ..ys] => NonEmptyList.reverseOnto { head = y, tail = [acc.head, ..acc.tail] } ys

--| The elements in the opposite order ([`NonEmptyList.reverseToList`]).
def NonEmptyList.reverse (xs: NonEmptyList a): NonEmptyList a := NonEmptyList.reverseOnto { head = xs.head, tail = [] } xs.tail

--| `xs` then `ys` ([`NonEmptyList.appendToList`]).
def NonEmptyList.append (xs: NonEmptyList a) (ys: NonEmptyList a): NonEmptyList a :=
  { head = xs.head, tail = List.append xs.tail ys.toList }

--| `xs` then the elements of a plain list ([`NonEmptyList.appendListToList`]).
def NonEmptyList.appendList (xs: NonEmptyList a) (ys: List a): NonEmptyList a :=
  { head = xs.head, tail = List.append xs.tail ys }

--| A plain list, then `xs` ([`NonEmptyList.prependListToList`]).
@[noReceiver]
def NonEmptyList.prependList (prefix: List a) (xs: NonEmptyList a): NonEmptyList a := match prefix with
  | [] => xs
  | [y, ..rest] => { head = y, tail = List.append rest xs.toList }

--| Sorting a `NonEmptyList` leaves a list with elements: the sorted list is as long as the original.
theorem NonEmptyList.sortByNotNil ∀ (xs: NonEmptyList a) (cmp: a → a → Ordering): List.sortBy xs.toList cmp ≠ [] :=
  sorted =>
    let same := List.permLength (List.sortBy xs.toList cmp) xs.toList (List.sortByPerm xs.toList cmp)
    let empty := rewrite sorted at same in same
    omega [empty]

--| Sorts by a comparison; stable, as `List.sortBy`. The result has the same elements ([`NonEmptyList.sortByToList`]).
def NonEmptyList.sortBy (xs: NonEmptyList a) (cmp: a → a → Ordering): NonEmptyList a :=
  List.toNonEmpty (List.sortBy xs.toList cmp) [nonEmpty := NonEmptyList.sortByNotNil xs cmp]

--| Sorts into ascending order by the type's `Ord`, as `List.sort` ([`NonEmptyList.sortToList`]).
def NonEmptyList.sort [auto ord: Ord a] (xs: NonEmptyList a): NonEmptyList a := NonEmptyList.sortBy xs Ord.compare

--| Whether `x` is one of the elements, by its `DecEq` ([`NonEmptyList.containsToList`]).
def NonEmptyList.contains [auto eq: DecEq a] (xs: NonEmptyList a) (x: a): Bool := List.contains xs.toList x

--| Whether `p` holds for some element ([`NonEmptyList.anyToList`]).
def NonEmptyList.any (xs: NonEmptyList a) (p: a → {e} Bool): {e} Bool := List.any xs.toList p

--| Whether `p` holds for every element ([`NonEmptyList.allToList`]).
def NonEmptyList.all (xs: NonEmptyList a) (p: a → {e} Bool): {e} Bool := List.all xs.toList p

--| `x` is one of the elements, as a proposition (what `x ∈ xs.toList` says).
@[noReceiver]
def NonEmptyList.Mem (x: a) (xs: NonEmptyList a): Prop := x ∈ xs.toList

--| `xs.contains x` is `True` exactly when `x` is one of the elements: its
--| reading, as `List.contains`'s.
@[reading]
theorem NonEmptyList.containsMem ∀ [auto eq: DecEq a] (xs: NonEmptyList a) (x: a): (xs.contains x = True) ↔ NonEmptyList.Mem x xs :=
  List.memContains xs.toList x

--| `xs.contains x` is `False` exactly when `x` is not an element.
@[reading]
theorem NonEmptyList.containsReadsFalse ∀ [auto eq: DecEq a] (xs: NonEmptyList a) (x: a): (xs.contains x = False) ↔ ¬(NonEmptyList.Mem x xs) :=
  List.containsReadsFalse xs.toList x

instance NonEmptyList.instShow [auto show: Show a]: Show (NonEmptyList a) :=
  Show.fromText (xs => Show.list (x => Show.toSource x) xs.toList)

theorem NonEmptyList.toListInjective ∀ (xs: NonEmptyList a) (ys: NonEmptyList a) (same: xs.toList = ys.toList): xs = ys :=
  match xs, ys with
    | { head = x, tail = s }, { head = y, tail = t } =>
      let heads := List.consInjectiveHead x y s t same
      let tails: s = t := Eq.cong (.drop 1) same
      rewrite heads in rewrite tails in rfl

--| Decides equality from a decision about the elements: the lists' ([`List.decEq`]).
@[noReceiver]
def NonEmptyList.decEq (d: (x: a) → (y: a) → Decidable (x = y)) (xs: NonEmptyList a) (ys: NonEmptyList a): Decidable (xs = ys) :=
  Decidable.elim (List.decEq d xs.toList ys.toList)
    (same => Decidable.yes (NonEmptyList.toListInjective xs ys same))
    (different => Decidable.no (equal => different (Eq.cong NonEmptyList.toList equal)))

instance NonEmptyList.instDecEq [auto decEq: DecEq a]: DecEq (NonEmptyList a) :=
  { decide = NonEmptyList.decEq (x y => DecEq.decide x y) }

--| Ordered as the lists are: lexicographically ([`NonEmptyList.compareToList`]).
instance NonEmptyList.instOrd [auto ord: Ord a]: Ord (NonEmptyList a) :=
  Ord.fromCompare (xs ys => Ord.compare xs.toList ys.toList)
    (xs ys h => NonEmptyList.toListInjective xs ys (List.instOrd.equal xs.toList ys.toList h))
    (xs ys => List.instOrd.flip xs.toList ys.toList)
    (xs ys zs => List.instOrd.trans xs.toList ys.toList zs.toList)

theorem NonEmptyList.compareToList ∀ [auto ord: Ord a] (xs: NonEmptyList a) (ys: NonEmptyList a): Ord.compare xs ys = Ord.compare xs.toList ys.toList := rfl
