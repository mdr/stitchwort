--| `Array a`: a sequence with constant-time access by position when a
--| program runs. To proofs an array is its list of elements, `toList`, and
--| every operation is defined on that list, so the list lemmas carry over and
--| nothing here is an axiom. At run time (`stitchwort run`, `--native`, the
--| playground) an array is one buffer, and its operations are natives bound
--| to these definitions by content hash (crates/rt/src/natives.rs).
--|
--| **Cost.** `get`, `getOr`, `getLt`, `size`, `set` and `push` take O(1).
--| `set`, `push` and `pop` change the buffer in place when nothing else
--| holds the array; when something does (an older version kept in a
--| variable, a map, a closure), they copy it first, which is O(n) but still
--| right. `stitchwort run` counts those copies and says so at the end of a
--| run that made many. Keep an array unshared by passing the new version on
--| and not using the old one again. Whole-array operations (`map`,
--| `foldLeft`, …) and `toList` are O(n). Under `--js` an array is a version
--| array: the newest version holds the buffer and each older one a record of
--| the change that tells it apart, so `get`, `set`, `push` and `pop` on the
--| newest are O(1) however many versions were made. An older version is
--| rebuilt (in a loop) the first time it is read or changed, which costs the
--| number of changes since. Whole-array operations are O(n) as above.
--|
--| **Reading.** Three ways, none of which can fail: `get` gives an `Option`,
--| `getOr` takes a fallback, and `getLt` takes a proof that the index is in
--| range, found by `auto`. Out of range, `set` and `modify` leave the array
--| unchanged, as `List.set` does.
-- docs/proposals/arrays.md.

--| A sequence with constant-time access by position when run: `[3, 1, 2].toArray`.
--| To proofs it is its list of elements, and every operation is defined on that list.
type Array (a: Type) = { toList: List a }

-- Building

--| The array of a list's elements, in order: `[3, 1, 2].toArray`. O(n).
def List.toArray (xs: List a): Array a := { toList = xs }

--| The array of a list's elements, in order: `Array.fromList xs` is `xs.toArray`.
def Array.fromList (xs: List a): Array a := { toList = xs }

--| The array with no elements.
def Array.empty: Array a := { toList = [] }

--| `count` copies of `x`: how a table indexed by number starts, `Array.replicate (count := 10) 0`.
def Array.replicate (count: Nat) (x: a): Array a := { toList = List.replicate count x }

--| The array of `f 0`, `f 1`, …, `f (count - 1)`.
def Array.tabulate (count: Nat) (f: Nat → a): Array a := { toList = List.map (List.range 0 count) f }

--| The vector's elements as an array.
def Vec.toArray (v: Vec a n): Array a := { toList = Vec.toList v }

-- Reading

--| The number of elements. O(1) when run.
def Array.size (array: Array a): Nat := List.length array.toList

--| Whether there are no elements.
def Array.isEmpty (array: Array a): Bool := array.size == 0

--| The element at `index`, counting from 0, or `None` past the end. O(1) when run.
def Array.get (array: Array a) (index: Nat): Option a := List.get array.toList index

--| The element at `index`, or `fallback` past the end. O(1) when run.
def Array.getOr (array: Array a) (index: Nat) (fallback: a): a := List.getOr array.toList index fallback

--| The element at `index` of a list longer than `index`: no fallback is needed.
@[tailrec]
def List.getLt: (xs: List a) → (index: Nat) → [auto ok: index < List.length xs] → a
  | [x, ..xs], Zero => x
  | [x, ..xs], Succ index => List.getLt xs index [ok := ok]

--| The element at an index in range, with the proof found by `auto` or passed
--| by name: `array.getLt 2` when `array` is known to have more than 2
--| elements. O(1) when run.
def Array.getLt (array: Array a) (index: Nat) [auto ok: index < array.size]: a :=
  List.getLt array.toList index [ok := ok]

--| The elements as a vector of the array's size.
def Array.toVec (array: Array a): Vec a array.size := Vec.fromList array.toList

-- Changing

--| The array with the element at `index` replaced by `value`; past the end,
--| unchanged. O(1) when run, in place when nothing else holds the array.
def Array.set (array: Array a) (index: Nat) (value: a): Array a := { toList = List.set array.toList index value }

--| The array with `value` added at the end. Amortised O(1) when run, in
--| place when nothing else holds the array.
def Array.push (array: Array a) (value: a): Array a := { toList = List.append array.toList [value] }

--| The array without its last element, and that element; `None` if it is
--| empty. O(1) when run, in place when nothing else holds the array.
def Array.pop (array: Array a): Option (Array a, a) := match List.reverse array.toList with
  | [] => None
  | [x, ..rest] => Some ({ toList = List.reverse rest }, x)

--| The array with `f` applied to the element at `index`; past the end,
--| unchanged. In place when nothing else holds the array.
def Array.modify (array: Array a) (index: Nat) (f: a → a): Array a := match array.get index with
  | Some x => array.set index (f x)
  | None => array

--| The array with the elements at `i` and `j` exchanged; unchanged if either
--| is past the end.
def Array.swap (array: Array a) (i j: Nat): Array a := match array.get i, array.get j with
  | Some x, Some y => (array.set i y).set j x
  | _, _ => array

-- The whole array: each is its list's operation, O(n).

--| `f` on each element, in order.
def Array.map (array: Array a) (f: a → b): Array b := { toList = List.map array.toList f }

--| `f` on each element and its index, in order.
def Array.mapWithIndex (array: Array a) (f: Nat → a → b): Array b := { toList = List.mapWithIndex array.toList f }

--| Left fold: `[x, y].toArray.foldLeft initial f` is `f (f initial x) y`.
def Array.foldLeft (array: Array a) (initial: b) (f: b → a → b): b := List.foldLeft array.toList initial f

--| Whether some element satisfies `p`.
def Array.any (array: Array a) (p: a → Bool): Bool := List.any array.toList p

--| Whether every element satisfies `p`.
def Array.all (array: Array a) (p: a → Bool): Bool := List.all array.toList p

--| How many elements satisfy `p`.
def Array.count (array: Array a) (p: a → Bool): Nat := List.count array.toList p

--| Each element with its index: `["a", "b"].toArray.withIndex` is `[(0, "a"), (1, "b")]`.
def Array.withIndex (array: Array a): List (Nat, a) := List.withIndex array.toList

--| The sum of the elements.
def Array.sum (array: Array Nat): Nat := List.sum array.toList

-- Equality, order and printing

--| Arrays with the same list are the same array.
theorem Array.toListInjective ∀ (a b: Array t) (h: a.toList = b.toList): a = b := match a, b with
  | { toList = xs }, { toList = ys } => Eq.cong (zs => ({ toList = zs }: Array t)) h

--| `==` on arrays: they're equal exactly when their lists are.
instance Array.instDecEq [auto decEq: DecEq a]: DecEq (Array a) := {
  decide = u v =>
    if h: u.toList = v.toList then Decidable.yes (Array.toListInjective u v h)
    else Decidable.no (e => h (Eq.cong (.toList) e))
}

--| Arrays in order: lexicographic, as their lists (`List.instOrd`).
instance Array.instOrd [auto ord: Ord a]: Ord (Array a) := Ord.byKey (.toList) Array.toListInjective

--| As the expression that builds it: `[3, 1, 2].toArray`.
instance Array.instShow [auto show: Show a]: Show (Array a) :=
  Show.fromText (array => Text.append (Show.list (x => Show.toSource x) array.toList) ".toArray")

-- Lemmas

--| Lists that agree at every index are equal (past the end, both give `None`).
theorem List.extGet ∀ (xs ys: List a) (h: ∀ (i: Nat) => List.get xs i = List.get ys i): xs = ys := match xs, ys with
  | [], [] => rfl
  | [], [y, ..ys] => Void.exfalso (Option.noneNotSome y (h 0))
  | [x, ..xs], [] => Void.exfalso (Option.noneNotSome x (Eq.sym (h 0)))
  | [x, ..xs], [y, ..ys] =>
    Eq.trans
      (Eq.cong (z => [z, ..xs]) (Option.someInjective (h 0)))
      (Eq.cong (Cons y) (List.extGet xs ys (i => h (Succ i))))

--| Arrays that agree at every index are equal.
theorem Array.ext ∀ (a b: Array t) (h: ∀ (i: Nat) => a.get i = b.get i): a = b :=
  Array.toListInjective a b (List.extGet a.toList b.toList h)

--| `toList` of the array of a list is the list.
theorem Array.toListFromList ∀ (xs: List a): (Array.fromList xs).toList = xs := rfl

--| `List.toArray` and `toList` are inverse.
theorem Array.toListToArray ∀ (xs: List a): xs.toArray.toList = xs := rfl

--| The array of an array's list is the array.
theorem Array.fromListToList ∀ (array: Array a): Array.fromList array.toList = array := match array with
  | { toList = xs } => rfl

--| The size is the list's length.
theorem Array.sizeToList ∀ (array: Array a): array.size = List.length array.toList := rfl

--| `getLt` finds what `get` finds.
theorem List.getLtGet ∀ (xs: List a) (i: Nat)
    (ok: i < List.length xs):
    List.get xs i = Some (List.getLt xs i [ok := ok]) :=
  match xs, i with
    | [x, ..xs], Zero => rfl
    | [x, ..xs], Succ i => List.getLtGet xs i ok

--| `getLt` finds what `get` finds.
theorem Array.getLtGet ∀ (array: Array a) (i: Nat)
    (ok: i < array.size):
    array.get i = Some (array.getLt i [ok := ok]) :=
  List.getLtGet array.toList i ok

--| `getOr` is `get` with the fallback for `None`.
theorem Array.getOrGet ∀ (array: Array a) (i: Nat) (d: a): array.getOr i d = (array.get i).getOrElse d :=
  List.getOrGet array.toList i d

--| An index is in range exactly when `get` finds something there.
theorem Array.getPast ∀ (array: Array a) (i: Nat) (h: array.size ≤ i): array.get i = None :=
  List.getPast array.toList i h

--| `set` keeps the size, whether or not the index is in range.
theorem Array.sizeSet ∀ (array: Array a) (i: Nat) (v: a): (array.set i v).size = array.size :=
  List.lengthSet array.toList i v

--| In range, `get` after a `set` finds the new value.
theorem Array.getSet ∀ (array: Array a) (i: Nat) (v: a) (h: i < array.size): (array.set i v).get i = Some v :=
  List.getSet array.toList i v h

--| At another index, `set` changes nothing `get` finds.
theorem Array.getSetOther ∀ (array: Array a) (i: Nat) (v: a) (j: Nat) (h: j ≠ i): (array.set i v).get j = array.get j :=
  List.getSetOther array.toList i v j h

--| In range, `getOr` after a `set` finds the new value, whatever the fallback.
theorem Array.getOrSet ∀ (array: Array a) (i: Nat) (v d: a) (h: i < array.size): (array.set i v).getOr i d = v :=
  Eq.trans (Array.getOrGet (array.set i v) i d) (Eq.cong (o => Option.getOrElse o d) (Array.getSet array i v h))

--| At another index, `set` changes nothing `getOr` finds.
theorem Array.getOrSetOther ∀ (array: Array a) (i: Nat) (v: a) (j: Nat) (d: a)
    (h: j ≠ i):
    (array.set i v).getOr j d = array.getOr j d :=
  Eq.trans
    (Array.getOrGet (array.set i v) j d)
    (Eq.trans
      (Eq.cong (o => Option.getOrElse o d) (Array.getSetOther array i v j h))
      (Eq.sym (Array.getOrGet array j d)))

--| Past the end, `set` leaves the array unchanged.
theorem Array.setPast ∀ (array: Array a) (i: Nat) (v: a) (h: array.size ≤ i): array.set i v = array :=
  Array.ext (array.set i v) array (j =>
    if same: j = i then
      Eq.trans
        (Array.getPast (array.set i v) j (rewrite Array.sizeSet array i v in rewrite same in h))
        (Eq.sym (Array.getPast array j (rewrite same in h)))
    else Array.getSetOther array i v j same)

--| `push` adds one to the size.
theorem Array.sizePush ∀ (array: Array a) (v: a): (array.push v).size = array.size + 1 :=
  List.lengthAppend array.toList [v]

--| `push` keeps the elements that were there.
theorem Array.getPush ∀ (array: Array a) (v: a) (i: Nat) (h: i < array.size): (array.push v).get i = array.get i :=
  List.getAppendLeft array.toList [v] i h

--| After a `push`, the last element is the new one.
theorem Array.getPushLast ∀ (array: Array a) (v: a): (array.push v).get array.size = Some v :=
  rewrite List.getAppendRight array.toList [v] array.size (Nat.leRefl array.size) in
    rewrite Nat.subSelf array.size in rfl

--| `pop` undoes `push`.
theorem Array.popPush ∀ (array: Array a) (v: a): (array.push v).pop = Some (array, v) :=
  rewrite List.reverseSnoc array.toList v in
    rewrite List.reverseReverse array.toList in rewrite Array.fromListToList array in rfl

--| `modify` keeps the size.
theorem Array.sizeModify ∀ (array: Array a) (i: Nat) (f: a → a): (array.modify i f).size = array.size :=
  match h: array.get i with
    | Some x => Array.sizeSet array i (f x)
    | None => rfl

--| `replicate` has `count` elements.
theorem Array.sizeReplicate ∀ (count: Nat) (x: a): (Array.replicate count x).size = count :=
  List.lengthReplicate x count

--| Every element of `replicate` is `x`.
theorem Array.getOrReplicate ∀ (count: Nat) (x: a) (i: Nat): (Array.replicate count x).getOr i x = x :=
  List.getOrReplicate x i count

--| `map` keeps the size.
theorem Array.sizeMap ∀ (array: Array a) (f: a → b): (array.map f).size = array.size := List.lengthMap array.toList f

--| `map` applies `f` at each index.
theorem Array.getMap ∀ (array: Array a) (f: a → b) (i: Nat): (array.map f).get i = (array.get i).map f :=
  List.getMap array.toList f i

--| `foldLeft` is the list's.
theorem Array.foldLeftToList ∀ (array: Array a) (initial: b) (f: b → a → b):
    array.foldLeft initial f = List.foldLeft array.toList initial f :=
  rfl

--| The vector of an array has the array's elements.
theorem Array.toVecToList ∀ (array: Array a): Vec.toList array.toVec = array.toList := Vec.toListFromList array.toList

--| A small array for the tests below: 3, 1 and 2.
def Array.example: Array Nat := [3, 1, 2].toArray

test "array: get" := Array.example.get 1 == Some 1 ∧ Array.example.get 3 == None
test "array: getOr" := Array.example.getOr 0 9 == 3 ∧ Array.example.getOr 5 9 == 9
test "array: getLt" := Array.example.getLt 2 == 2
test "array: size" := Array.example.size == 3 ∧ (Array.empty: Array Nat).size == 0 ∧ (Array.empty: Array Nat).isEmpty
test "array: set" := (Array.example.set 1 7).toList == [3, 7, 2]
test "array: set past the end leaves it" := (Array.example.set 3 7).toList == [3, 1, 2]
test "array: push and pop" :=
  (Array.example.push 4).toList == [3, 1, 2, 4] ∧ Array.example.pop == Some ([3, 1].toArray, 2)
test "array: pop of empty" := (Array.empty: Array Nat).pop == None
test "array: modify" :=
  (Array.example.modify 0 (x => x * 10)).toList == [30, 1, 2] ∧ Array.example.modify 9 Succ == Array.example
test "array: swap" := (Array.example.swap 0 2).toList == [2, 1, 3] ∧ Array.example.swap 0 5 == Array.example
test "array: replicate and tabulate" :=
  (Array.replicate 3 'x').toList == ['x', 'x', 'x'] ∧ (Array.tabulate 4 (i => i * i)).toList == [0, 1, 4, 9]
test "array: whole-array operations" :=
  (Array.example.map Succ).toList == [4, 2, 3]
    ∧ Array.example.foldLeft 0 (+) == 6
    ∧ Array.example.sum == 6
    ∧ Array.example.count (x => x > 1) == 2
    ∧ Array.example.any (x => x == 2)
    ∧ Array.example.all (x => x > 0)
    ∧ Array.example.withIndex == [(0, 3), (1, 1), (2, 2)]
    ∧ (Array.example.mapWithIndex (i x => i + x)).toList == [3, 2, 4]
test "array: show" := Show.toText Array.example == "[3, 1, 2].toArray"
test "array: order" := [1, 2].toArray < [1, 3].toArray
