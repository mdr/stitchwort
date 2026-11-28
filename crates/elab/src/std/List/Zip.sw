--| Lemmas about zipping and indexing: `zipWith` with running accumulations,
--| `get`, `mapAccumLeft`, `All2`, and `zipWith`/`append` facts, with the
--| examples and tests that use them.

--| What `g` keeps of an element (`h`, an id say) doesn't depend on the other
--| list, so mapping it over the zip is mapping over the first list.
theorem List.mapZipWithLeft ∀ (h: c → d) (k: a → d) (g: a → b → c)
    (same: ∀ (x: a) (y: b) => h (g x y) = k x)
    (xs: List a) (ys: List b)
    (le: List.length xs ≤ List.length ys):
    List.map (List.zipWith xs ys g) h = List.map xs k :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [y, ..ys] => rewrite same x y, List.mapZipWithLeft h k g same xs ys le

-- `List.get`, the element at an index if there is one: it is `Some` exactly
-- within the list, what it finds is an element, and it goes through `map`,
-- `zipWith`, `append` and `take`. (`List.getOrGet`, std/List/Index.sw, is
-- `List.getOr` from it.)

--| `get` finds something exactly when the index is within the list.
theorem List.isSomeGet ∀ (xs: List a) (k: Nat): Option.isSome (List.get xs k) = Nat.leq (Succ k) (List.length xs) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.isSomeGet xs k

theorem List.getInRange ∀ (xs: List a) (k: Nat): k < List.length xs ↔ Option.isSome (List.get xs k) = True :=
  { forward = h => Eq.trans (List.isSomeGet xs k) h, backward = h => Eq.trans (List.isSomeGet xs k).flipped h }

--| Past the end, `get` finds nothing.
theorem List.getPast ∀ (xs: List a) (k: Nat) (h: List.length xs ≤ k): List.get xs k = None := match xs, k with
  | [], k => byComputing
  | [x, ..xs], Succ k => List.getPast xs k h

--| An index where `get` finds something is inside the list; the converse is
--| [`List.getInRange`].
theorem List.getSomeLt ∀ (xs: List a) (i: Nat) (x: a) (found: List.get xs i = Some x): i < List.length xs :=
  match xs, i, x with
    | [x, ..xs], Zero, y => arithmetic
    | [x, ..xs], Succ i, y => arithmetic [List.getSomeLt xs i y found]

--| What `get` finds is an element of the list.
theorem List.memOfGet ∀ (xs: List a) (k: Nat) (v: a) (h: List.get xs k = Some v): v ∈ xs := match xs, k with
  | [x, ..xs], Zero => Inl (Option.someInjective h)
  | [x, ..xs], Succ k => Inr (List.memOfGet xs k v h)

--| Setting an element keeps the length, whether or not the index is inside.
theorem List.lengthSet ∀ (xs: List a) (i: Nat) (v: a): List.length (List.set xs i v) = List.length xs :=
  match xs, i with
    | [], i => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ i => Eq.cong Succ (List.lengthSet xs i v)

--| Inside the list, `get` after a `set` finds the new value.
theorem List.getSet ∀ (xs: List a) (i: Nat) (v: a) (below: i < List.length xs): List.get (List.set xs i v) i = Some v :=
  match xs, i with
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ i => List.getSet xs i v (arithmetic)

--| At another index, `set` changes nothing `get` finds there; past the end
--| both finds nothing.
theorem List.getSetOther ∀ (xs: List a) (i: Nat) (v: a) (j: Nat)
    (differ: j ≠ i):
    List.get (List.set xs i v) j = List.get xs j :=
  match xs, i, j with
    | [], i, j => byComputing
    | [x, ..xs], Zero, Zero => (differ byComputing).impossible
    | [x, ..xs], Zero, Succ j => byComputing
    | [x, ..xs], Succ i, Zero => byComputing
    | [x, ..xs], Succ i, Succ j => List.getSetOther xs i v j (same => differ (Eq.cong Succ same))

theorem List.getMap ∀ (xs: List a) (f: a → b) (k: Nat): List.get (List.map xs f) k = Option.map (List.get xs k) f :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getMap xs f k

--| `withIndexFrom` is as long as the list; element k is the
--| list's element k with k (counted from `start`).
theorem List.lengthWithIndexFrom ∀ (start: Nat) (xs: List a):
    List.length (List.withIndexFrom start xs) = List.length xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => Eq.cong Succ (List.lengthWithIndexFrom (Succ start) xs)

theorem List.lengthWithIndex ∀ (xs: List a): List.length (List.withIndex xs) = List.length xs :=
  List.lengthWithIndexFrom 0 xs

theorem List.getWithIndexFrom ∀ (start: Nat) (xs: List a) (k: Nat):
    List.get (List.withIndexFrom start xs) k = Option.map (List.get xs k) (x => MkPair (start + k) x) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => rewrite Nat.addZero start
    | [x, ..xs], Succ k => rewrite Nat.addSucc start k then List.getWithIndexFrom (Succ start) xs k

theorem List.getWithIndex ∀ (xs: List a) (k: Nat):
    List.get (List.withIndex xs) k = Option.map (List.get xs k) (x => MkPair k x) :=
  List.getWithIndexFrom 0 xs k

--| `mapWithIndex` keeps the length, and element k is `f k` of the list's
--| element k.
theorem List.lengthMapWithIndex ∀ (xs: List a) (f: Nat → a → b):
    List.length (List.mapWithIndex xs f) = List.length xs :=
  Eq.trans (List.lengthMap (List.withIndex xs) (pair => f pair.fst pair.snd)) (List.lengthWithIndex xs)

theorem List.getMapWithIndex ∀ (xs: List a) (f: Nat → a → b) (k: Nat):
    List.get (List.mapWithIndex xs f) k = Option.map (List.get xs k) (f k) :=
  let mapped: List.get (List.mapWithIndex xs f) k
    = Option.map (Option.map (List.get xs k) (x => MkPair k x)) (pair => f pair.fst pair.snd) :=
    rewrite <- List.getWithIndex xs k then List.getMap (List.withIndex xs) (pair => f pair.fst pair.snd) k
  rewrite mapped then match List.get xs k with | None | Some _ => byComputing

--| `zipWith` has `f x y` where both lists have an element, `x` and `y`.
theorem List.getZipWith ∀ (f: a → b → c) (xs: List a) (ys: List b) (k: Nat):
    List.get (List.zipWith xs ys f) k = Option.flatMap (List.get xs k) (x => Option.map (List.get ys k) (f x)) :=
  match xs, ys, k with
    | [], ys, k => byComputing
    | [x, ..xs], [], Zero => byComputing
    | [x, ..xs], [], Succ k =>
      match c: List.get xs k with
        | None | Some _ => byComputing
    | [x, ..xs], [y, ..ys], Zero => byComputing
    | [x, ..xs], [y, ..ys], Succ k => List.getZipWith f xs ys k

--| `zip`, `zipWith3` and `zipWith4` have the combined elements where every
--| list has one.
theorem List.getZip ∀ (xs: List a) (ys: List b) (k: Nat):
    List.get (List.zip xs ys) k = Option.map2 MkPair (List.get xs k) (List.get ys k) :=
  match xs, ys, k with
    | [], ys, k => byComputing
    | [x, ..xs], [], k => (Option.map2None MkPair _).flipped
    | [x, ..xs], [y, ..ys], Zero => byComputing
    | [x, ..xs], [y, ..ys], Succ k => List.getZip xs ys k

theorem List.getZipWith3 ∀ (f: a → b → c → d) (xs: List a) (ys: List b) (zs: List c) (k: Nat):
    List.get (List.zipWith3 xs ys zs f) k = Option.map3 f (List.get xs k) (List.get ys k) (List.get zs k) :=
  match xs, ys, zs, k with
    | [], ys, zs, k => byComputing
    | [x, ..xs], [], zs, k => (Option.map3None2 f _ _).flipped
    | [x, ..xs], [y, ..ys], [], k => (Option.map3None3 f _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], Zero => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], Succ k => List.getZipWith3 f xs ys zs k

theorem List.getZipWith4 ∀ (f: a → b → c → d → e) (xs: List a) (ys: List b) (zs: List c) (ws: List d) (k: Nat):
    List.get (List.zipWith4 xs ys zs ws f) k
      = Option.map4 f (List.get xs k) (List.get ys k) (List.get zs k) (List.get ws k) :=
  match xs, ys, zs, ws, k with
    | [], ys, zs, ws, k => byComputing
    | [x, ..xs], [], zs, ws, k => (Option.map4None2 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [], ws, k => (Option.map4None3 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], [], k => (Option.map4None4 f _ _ _).flipped
    | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Zero => byComputing
    | [x, ..xs], [y, ..ys], [z, ..zs], [w, ..ws], Succ k => List.getZipWith4 f xs ys zs ws k

theorem List.getZipWith3Example: List.get (List.zipWith3 [1, 2] [10, 20, 30] [100, 200] (x y z => x + y + z)) 1
      = Some 222 :=
  byComputing

--| `append`: the first list's element, else the second's, counting on from
--| the end of the first.
theorem List.getAppend ∀ (xs ys: List a) (k: Nat):
    List.get (List.append xs ys) k = Option.orElse (List.get xs k) (List.get ys (k - List.length xs)) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getAppend xs ys k

theorem List.getAppendLeft ∀ (xs ys: List a) (k: Nat)
    (h: k < List.length xs):
    List.get (List.append xs ys) k = List.get xs k :=
  match xs, k with
    | [x, ..xs], Zero => byComputing
    | [x, ..xs], Succ k => List.getAppendLeft xs ys k h

theorem List.getAppendRight ∀ (xs ys: List a) (k: Nat)
    (h: List.length xs ≤ k):
    List.get (List.append xs ys) k = List.get ys (k - List.length xs) :=
  match xs, k with
    | [], k => byComputing
    | [x, ..xs], Succ k => List.getAppendRight xs ys k h

--| `take n` keeps the elements before `n`, and nothing from `n` on.
theorem List.getTake ∀ (xs: List a) (n k: Nat) (h: k < n): List.get (List.take xs n) k = List.get xs k :=
  match xs, n, k with
    | [], Succ n, k => byComputing
    | [x, ..xs], Succ n, Zero => byComputing
    | [x, ..xs], Succ n, Succ k => List.getTake xs n k h

theorem List.getTakePast ∀ (xs: List a) (n k: Nat) (h: n ≤ k): List.get (List.take xs n) k = None := match xs, n, k with
  | xs, Zero, k => byComputing
  | [], Succ n, k => byComputing
  | [x, ..xs], Succ n, Succ k => List.getTakePast xs n k h

--| Index j after dropping k is index k + j before.
theorem List.getDrop ∀ (xs: List a) (k j: Nat): List.get (List.drop xs k) j = List.get xs (k + j) := match xs, k with
  | xs, Zero => byComputing
  | [], Succ k => byComputing
  | [x, ..xs], Succ k => List.getDrop xs k j

--| What `List.transposeN`'s columns are: column i holds element i of every
--| row that has one. From column `p` on, for the rows with their first `p`
--| elements dropped (`transposeN`'s own loop):
theorem List.transposeNColumnsFrom ∀ (rows: List (List a)) (k p: Nat):
    List.transposeN k (List.map rows (row => List.drop row p))
      = List.map (List.rangeFrom k p) (i => List.filterMap rows (row => List.get row i)) :=
  match k with
    | Zero => byComputing
    | Succ k =>
      rewrite List.filterMapMap rows (x => List.get x 0) (row => List.drop row p),
          List.mapMap rows (x => List.drop x 1) (row => List.drop row p),
          List.getDrop _ p 0,
          Nat.addZero p,
          <- List.dropAdd p 1 then
        Eq.cong
          (later => [List.filterMap rows (row => List.get row p), ..later])
          (List.transposeNColumnsFrom rows k (p + 1))

--| `transposeN k` gives column i, for each i below k, as element i of every row that has one.
theorem List.transposeNColumns ∀ (rows: List (List a)) (k: Nat):
    List.transposeN k rows = List.map (List.range 0 k) (i => List.filterMap rows (row => List.get row i)) :=
  Eq.trans (Eq.cong (rows => List.transposeN k rows) (List.mapId rows).flipped) (List.transposeNColumnsFrom rows k 0)

--| Column i of `List.transpose` holds element i of every row that has one,
--| for each i below the first row's length.
theorem List.transposeColumns ∀ (rows: List (List a)):
    List.transpose rows
      = List.map (List.range 0 (List.length (List.headOr rows []))) (i =>
        List.filterMap rows (row => List.get row i)) :=
  List.transposeNColumns rows (List.length (List.headOr rows []))

theorem List.getExample: List.get (List.append [1, 2] (List.map [3, 4] Succ)) 3 = Some 5 := byComputing

--| For any list of successors, what `get` finds is not zero.
theorem List.getMapExample ∀ (xs: List Nat) (k v: Nat) (h: List.get (List.map xs Succ) k = Some v): v ≠ 0 :=
  Option.mapEqSome (List.get xs k) Succ v (Eq.trans (List.getMap xs Succ k).flipped h) (u found e =>
    rewrite <- e then Nat.succNotZero u)

--| `List.All2 r xs ys`: the lists are as long, and `r` holds of each pair of
--| elements at the same place (Coq's `Forall2`, Lean's `List.Forall₂`). What
--| [`Parse.eachLineReads`] says of the lines and the values read from them.
@[noReceiver]
def List.All2 (r: a → b → Prop): (xs: List a) → (ys: List b) → Prop
  | [], [] => Unit
  | [x, ..xs], [y, ..ys] => r x y ∧ List.All2 r xs ys
  | [], [y, ..ys] => Void
  | [x, ..xs], [] => Void

theorem List.all2Weaken ∀ [r s: a → b → Prop] (implies: ∀ (x: a) (y: b) => r x y → s x y) (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 s xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both (implies x y all.left) (List.all2Weaken implies xs ys all.right)

--| [`List.all2Weaken`] where the implication may use that the second element
--| is in `ys`: a fact about all of `ys` (a grid's rows are all as long as its
--| width) joins the relation.
theorem List.all2WeakenMem ∀ [r s: a → b → Prop] (xs: List a)
    (ys: List b) (implies: ∀ (x: a) (y: b) => y ∈ ys → r x y → s x y)
    (all: List.All2 r xs ys):
    List.All2 s xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] =>
      Both
        (implies x y (Inl byComputing) all.left)
        (List.all2WeakenMem xs ys (x2 y2 member => implies x2 y2 (Inr member)) all.right)

--| Where each element is `f` of its partner, the list is the partners mapped.
theorem List.all2Map ∀ [f: b → a] (xs: List a) (ys: List b) (all: List.All2 (x y => x = f y) xs ys): xs = ys.map f :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite And.left all, List.all2Map xs ys all.right

theorem List.all2MapLeft ∀ (f: a → c) (r: c → b → Prop) (xs: List a) (ys: List b)
    (all: List.All2 (x y => r (f x) y) xs ys):
    List.All2 r (xs.map f) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2MapLeft f r xs ys all.right)

--| The converse of [`List.all2MapLeft`]: a relation between the mapped list
--| and the values holds of each element's image.
theorem List.all2OfMapLeft ∀ (f: a → c) (r: c → b → Prop) (xs: List a) (ys: List b)
    (all: List.All2 r (xs.map f) ys):
    List.All2 (x y => r (f x) y) xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfMapLeft f r xs ys all.right)

--| The right-hand counterpart of [`List.all2OfMapLeft`]: a relation between
--| the left list and the mapped right list holds of each element's image.
theorem List.all2OfMapRight ∀ (g: b → c) (r: a → c → Prop) (xs: List a) (ys: List b)
    (all: List.All2 r xs (ys.map g)):
    List.All2 (x y => r x (g y)) xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfMapRight g r xs ys all.right)

--| Mapping two functions over one list gives lists related pointwise, when
--| the related values are `f x` and `g x` for each member `x`.
theorem List.all2MapBoth ∀ (r: b → c → Prop) (f: a → b) (g: a → c)
    (xs: List a) (pointwise: ∀ (x: a) => x ∈ xs → r (f x) (g x)):
    List.All2 r (xs.map f) (xs.map g) :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      Both (pointwise x (Inl byComputing)) (List.all2MapBoth r f g xs (y member => pointwise y (Inr member)))

--| A function that splits over `cons`, `f [x, ..rest] = join (key x) (f rest)`, gives the same on two lists
--| that are alike (`List.All2 rel`) when `rel`-alike elements have the same `key`. `f` is typically a
--| walk that collects something from each element, and `join` is `cons` or `++`.
theorem List.all2Join ∀ [f: List a → c] [key: a → k] [rel: a → a → Prop] (join: k → c → c)
    (cons: ∀ (x: a) (rest: List a) => f [x, ..rest] = join (key x) (f rest))
    (same: ∀ (x y: a) => rel x y → key x = key y) (xs ys: List a)
    (alike: List.All2 rel xs ys):
    f xs = f ys :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..rest], [y, ..restTwin] =>
      calc f [x, ..rest]
        _ = join (key x) (f rest) := cons x rest
        _ = join (key y) (f restTwin) :=
          Eq.cong2 join (same x y alike.left) (List.all2Join join cons same rest restTwin alike.right)
        _ = f [y, ..restTwin] := Eq.flipped (cons y restTwin)

--| Related lists are as long: the length half of `List.All2`.
theorem List.all2Length ∀ (r: a → b → Prop) (xs: List a) (ys: List b) (all: List.All2 r xs ys): xs.length = ys.length :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => Eq.cong Succ (List.all2Length r xs ys all.right)

--| Related lists joined are related: `xs ++ more` and `ys ++ moreTwin`.
theorem List.all2Append ∀ [r: a → b → Prop] (xs: List a) (ys: List b) (more: List a) (moreTwin: List b)
    (first: List.All2 r xs ys)
    (second: List.All2 r more moreTwin):
    List.All2 r (xs ++ more) (ys ++ moreTwin) :=
  match xs, ys with
    | [], [] => second
    | [x, ..xs], [y, ..ys] => Both first.left (List.all2Append xs ys more moreTwin first.right second)

--| Related lists reversed are related.
theorem List.all2Reverse ∀ [r: a → b → Prop] (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 r xs.reverse ys.reverse :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] =>
      rewrite List.reverseCons x xs, List.reverseCons y ys then
        List.all2Append xs.reverse ys.reverse [x] [y] (List.all2Reverse xs ys all.right) (Both all.left Trivial)

--| Numbering the left list changes nothing a relation of the elements sees.
theorem List.all2WithIndex ∀ (r: a → b → Prop) (start: Nat) (xs: List a) (ys: List b)
    (all: List.All2 (entry y => r entry.snd y) (List.withIndexFrom start xs) ys):
    List.All2 r xs ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2WithIndex r (Succ start) xs ys all.right)

--| The converse of [`List.all2WithIndex`]: a relation of the elements holds
--| of the numbered list too, ignoring the numbers.
theorem List.all2OfWithIndex ∀ (r: a → b → Prop) (start: Nat) (xs: List a) (ys: List b)
    (all: List.All2 r xs ys):
    List.All2 (entry y => r entry.snd y) (List.withIndexFrom start xs) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [x, ..xs], [y, ..ys] => Both all.left (List.all2OfWithIndex r (Succ start) xs ys all.right)

--| Zipped lists are as long as the shorter of the two.
theorem List.lengthZipWith ∀ (f: a → b → c) (xs: List a) (ys: List b):
    List.length (List.zipWith xs ys f) = Nat.min (List.length xs) (List.length ys) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.lengthZipWith f xs ys, Nat.minSucc (List.length xs) (List.length ys)

--| Zipping appended lists, when the first parts have the same length, is
--| appending what the parts zip to.
theorem List.zipWithAppend ∀ (f: a → b → c) (xs2: List a) (ys2: List b) (xs: List a) (ys: List b)
    (same: List.length xs = List.length ys):
    List.zipWith (xs ++ xs2) (ys ++ ys2) f = List.zipWith xs ys f ++ List.zipWith xs2 ys2 f :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithAppend f xs2 ys2 xs ys (Nat.succInjective same)
    | [], [y, ..ys] => Void.impossible arithmetic
    | [x, ..xs], [] => Void.impossible arithmetic

--| Zipping two lists of the same length, each with one more element on the
--| end, adds `f` of the two to the end.
theorem List.zipWithSnoc ∀ (f: a → b → c) (x: a) (y: b) (xs: List a) (ys: List b)
    (same: List.length xs = List.length ys):
    List.zipWith (xs ++ [x]) (ys ++ [y]) f = List.zipWith xs ys f ++ [f x y] :=
  rewrite List.zipWithAppend f [x] [y] xs ys same

--| Mapping the first list before zipping is zipping with `f` composed with
--| the map.
theorem List.zipWithMapLeft ∀ (f: b → c → d) (g: a → b) (xs: List a) (ys: List c):
    List.zipWith (List.map xs g) ys f = List.zipWith xs ys (x y => f (g x) y) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithMapLeft f g xs ys

--| Mapping the second list before zipping is zipping with `f` composed with
--| the map.
theorem List.zipWithMapRight ∀ (f: a → c → d) (g: b → c) (xs: List a) (ys: List b):
    List.zipWith xs (List.map ys g) f = List.zipWith xs ys (x y => f x (g y)) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithMapRight f g xs ys

--| Mapping over zipped lists is zipping with `f` followed by the map.
theorem List.mapZipWith ∀ (f: a → b → c) (g: c → d) (xs: List a) (ys: List b):
    List.map (List.zipWith xs ys f) g = List.zipWith xs ys (x y => g (f x y)) :=
  match xs, ys with
    | [], ys => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.mapZipWith f g xs ys

--| Zipping with the arguments to `f` swapped is zipping the lists the other
--| way round.
theorem List.zipWithSwap ∀ (f: a → b → c) (xs: List a) (ys: List b):
    List.zipWith ys xs (y x => f x y) = List.zipWith xs ys f :=
  match xs, ys with
    | [], [] | [_, .._] => byComputing
    | [x, ..xs], [] => byComputing
    | [x, ..xs], [y, ..ys] => rewrite List.zipWithSwap f xs ys

--| Chaining two `All2` facts through the middle list: if each `x`, `y`, `z`
--| at the same place with `r x y` and `s y z` have `t x z`, then `r` from
--| `xs` to `ys` and `s` from `ys` to `zs` give `t` from `xs` to `zs`.
theorem List.all2Compose ∀ [r: a → b → Prop] [s: b → c → Prop] [t: a → c → Prop]
    (link: ∀ (x: a) (y: b) (z: c) => r x y → s y z → t x z) (xs: List a) (ys: List b) (zs: List c)
    (first: List.All2 r xs ys)
    (second: List.All2 s ys zs):
    List.All2 t xs zs :=
  match xs, ys, zs with
    | [], [], [] => Trivial
    | [x, ..xs], [y, ..ys], [z, ..zs] =>
      Both (link x y z first.left second.left) (List.all2Compose link xs ys zs first.right second.right)

--| A list is related to itself, place by place, by any relation that holds
--| of every element and itself.
theorem List.all2Refl ∀ (r: a → a → Prop) (refl: ∀ (x: a) => r x x) (xs: List a): List.All2 r xs xs := match xs with
  | [] => Trivial
  | [x, ..xs] => Both (refl x) (List.all2Refl r refl xs)

--| Against a list of `n` copies of `y`, every element of `xs` is related to
--| `y`. The converse is [`List.all2ReplicateOf`].
theorem List.all2Replicate ∀ [r: a → b → Prop] (y: b):
    ∀ (xs: List a) (n: Nat) => List.All2 r xs (List.replicate n y) → ∀ (x: a) => x ∈ xs → r x y
  | [], n, all, x, member => member.impossible
  | [z, ..zs], Zero, all, x, member => all.impossible
  | [z, ..zs], Succ n, all, x, Inl same => rewrite <- same then And.left all
  | [z, ..zs], Succ n, all, x, Inr later => List.all2Replicate y zs n all.right x later

--| A list of `n` elements, each related to `y`, is related place by place to
--| `n` copies of `y`. The converse is [`List.all2Replicate`].
theorem List.all2ReplicateOf ∀ [r: a → b → Prop] (y: b) (xs: List a) (n: Nat)
    (same: xs.length = n) (related: ∀ (x: a) => x ∈ xs → r x y):
    List.All2 r xs (List.replicate n y) :=
  match xs, n with
    | [], Zero => Trivial
    | [], Succ n => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], Succ n =>
      Both
        (related x (Inl byComputing))
        (List.all2ReplicateOf y xs n (Nat.succInjective same) (z member => related z (Inr member)))

--| Zipping two lists of the same length gives a list of that length (unlike
--| [`List.lengthZipWith`], which gives the shorter of the two).
theorem List.lengthZipWithEq ∀ (f: a → b → c) (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    (List.zipWith xs ys f).length = xs.length :=
  match xs, ys with
    | [], [] => byComputing
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Eq.cong Succ (List.lengthZipWithEq f xs ys (Nat.succInjective same))

--| Where `r` holds of every result of `f` and its first argument, the zip of
--| two lists of the same length is related, place by place, to the first.
theorem List.all2ZipWithLeft ∀ (f: a → b → c) (r: c → a → Prop) (pointwise: ∀ (x: a) (y: b) => r (f x y) x)
    (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    List.All2 r (List.zipWith xs ys f) xs :=
  match xs, ys with
    | [], [] => Trivial
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Both (pointwise x y) (List.all2ZipWithLeft f r pointwise xs ys (Nat.succInjective same))

--| Where `r` holds of every result of `f` and its second argument, the zip of
--| two lists of the same length is related, place by place, to the second.
theorem List.all2ZipWithRight ∀ (f: a → b → c) (r: c → b → Prop) (pointwise: ∀ (x: a) (y: b) => r (f x y) y)
    (xs: List a) (ys: List b)
    (same: xs.length = ys.length):
    List.All2 r (List.zipWith xs ys f) ys :=
  match xs, ys with
    | [], [] => Trivial
    | [], [y, ..ys] => (Nat.zeroNotSucc _ same).impossible
    | [x, ..xs], [] => (Nat.succNotZero _ same).impossible
    | [x, ..xs], [y, ..ys] => Both (pointwise x y) (List.all2ZipWithRight f r pointwise xs ys (Nat.succInjective same))

--| A list with no element equal to `x` counts none: `xs.contains x` is
--| `False` exactly when `x` is not among `xs`.
theorem List.countZeroOfNotContains ∀ [auto eq: DecEq a] (xs: List a) (x: a)
    (absent: xs.contains x = False):
    xs.count (y => y == x) = 0 :=
  List.countNone xs (y => y == x) (y member =>
    match same: y == x with
      | True => Void.impossible (Bool.falseNotTrue (Eq.trans absent.flipped (rewrite <- same.read then member)))
      | False => byComputing)

--| If every value occurs in `xs` at most once (counted with `==`), `xs` has
--| no repeats. Unlike [`List.distinctOfOccurrences`] this needs no key, and
--| it holds of a list being built up, where each step changes one count.
theorem List.distinctOfCounts ∀ [auto eq: DecEq a] (xs: List a)
    (counts: ∀ (x: a) => xs.count (y => y == x) ≤ 1):
    xs.Distinct :=
  match xs with
    | [] => Trivial
    | [x, ..xs] =>
      Both
        (member =>
          let here := counts x
          let positive := List.countPositive xs (y => y == x) x member (DecEq.refl x)
          let split := List.countCons xs x (y => y == x)
          let self := DecEq.refl x
          rewrite split, self at here then arithmetic)
        (List.distinctOfCounts xs (other =>
          let here := counts other
          let split := List.countCons xs x (y => y == other)
          rewrite split at here then arithmetic))

test "List.zipWith lemmas" :=
  List.zipWith ([1, 2] ++ [3]) ([10, 20] ++ [30, 40]) (x y => x + y) == [11, 22, 33]
    ∧ List.length (List.zipWith [1, 2, 3] [4, 5] (x y => x + y)) == 2

--| Equal non-empty lists have equal tails; [`List.consInjectiveHead`] gives the heads.
theorem List.consTailEq ∀ (x y: a) (xs ys: List a) (same: [x, ..xs] = [y, ..ys]): xs = ys :=
  Eq.cong (list => list.drop 1) same

--| Consing equal heads onto equal tails gives equal lists.
theorem List.consEqOfEq ∀ (x y: a) (xs ys: List a) (head: x = y) (tail: xs = ys): [x, ..xs] = [y, ..ys] :=
  rewrite head, tail

--| Two joined lists that are equal, with equal first parts in length, have equal first parts and equal second parts.
theorem List.appendCancel ∀ (a c b d: List x) (joined: a ++ b = c ++ d) (lengths: a.length = c.length): a = c ∧ b = d :=
  match a, c with
    | [], [] => (byComputing, joined)
    | [], [q, ..qs] => Void.impossible (Nat.zeroNotSucc qs.length lengths)
    | [p, ..ps], [] => Void.impossible (Nat.succNotZero ps.length lengths)
    | [p, ..ps], [q, ..qs] =>
      let headSame: p = q := Eq.cong (all => all.headOr p) joined
      let (restSame, tailSame) :=
        List.appendCancel ps qs b d (Eq.cong (all => all.drop 1) joined) (Eq.cong (n => n - 1) lengths)
      (List.consEqOfEq p q ps qs headSame restSame, tailSame)

--| The head of a join with a non-empty front is the front's head.
theorem List.headAppend ∀ (front back: List a) (filled: front ≠ []): (front ++ back).head = front.head :=
  match front, filled with
    | [], never => (never byComputing).impossible
    | [first, ..rest], _ => byComputing

--| The head of a three-part join with a non-empty front is the front's head.
theorem List.headAppendMiddle ∀ (front middle back: List a)
    (nonEmpty: front ≠ []):
    ((front ++ middle) ++ back).head = front.head :=
  match front, nonEmpty with
    | [], nonEmpty => (nonEmpty byComputing).impossible
    | [first, ..more], nonEmpty => byComputing

--| `reverseOnto` a non-empty accumulator is non-empty.
theorem List.reverseOntoNonEmpty ∀ (xs acc: List a)
    (filled: acc.isEmpty = False):
    (xs.reverseOnto acc).isEmpty = False :=
  match xs with
    | [] => filled
    | [x, ..rest] => List.reverseOntoNonEmpty rest [x, ..acc] byComputing

--| `reverseOnto` is empty exactly when both the list and the accumulator are.
theorem List.isEmptyReverseOnto ∀ (xs acc: List a): (xs.reverseOnto acc).isEmpty = (xs.isEmpty && acc.isEmpty) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite List.isEmptyReverseOnto rest [x, ..acc] then cases

--| A test over a join holds of both parts: `all` over `++` is the `&&` of the two `all`s.
theorem List.allAppendAnd ∀ (xs ys: List a) (p: a → Bool): (xs ++ ys).all p = (xs.all p && ys.all p) := match xs with
  | [] => byComputing
  | [x, ..rest] =>
    match p x with
      | True => List.allAppendAnd rest ys p
      | False => byComputing

--| A test that holds of both of two lists holds of their join.
theorem List.allAppendTrue ∀ (xs ys: List a) (p: a → Bool)
    (first: xs.all p = True)
    (second: ys.all p = True):
    (xs ++ ys).all p = True :=
  match xs with
    | [] => second
    | [x, ..rest] => Bool.andIntro (Bool.andLeft first) (List.allAppendTrue rest ys p (Bool.andRight first) second)

--| A test that holds of a list and of an accumulator holds of the list reversed onto the accumulator.
theorem List.allReverseOntoTrue ∀ (p: a → Bool) (xs acc: List a)
    (all: xs.all p = True)
    (allAcc: acc.all p = True):
    (xs.reverseOnto acc).all p = True :=
  match xs with
    | [] => allAcc
    | [x, ..more] =>
      List.allReverseOntoTrue p more [x, ..acc] (Bool.andRight all) (Bool.andIntro (Bool.andLeft all) allAcc)

--| `all` over a list reversed onto an accumulator is the `&&` of the `all`s of the two.
theorem List.allReverseOntoAnd ∀ (xs acc: List a) (p: a → Bool): (xs.reverseOnto acc).all p = (xs.all p && acc.all p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc (rest.reverseOnto [x, ..acc]).all p
        _ = (rest.all p && [x, ..acc].all p) := List.allReverseOntoAnd rest [x, ..acc] p
        _ = ([x, ..rest].all p && acc.all p) := cases

--| A test that holds of a list holds of its reverse.
theorem List.allReverseTrue ∀ (p: a → Bool) (xs: List a) (all: xs.all p = True): xs.reverse.all p = True :=
  List.allReverseOntoTrue p xs [] all byComputing

--| A test that holds of a join holds of its second part.
theorem List.allAppendRightTrue ∀ (p: a → Bool) (xs ys: List a) (all: (xs ++ ys).all p = True): ys.all p = True :=
  match xs with
    | [] => all
    | [x, ..more] => List.allAppendRightTrue p more ys (Bool.andRight all)

--| A test that holds of a non-empty list holds of its head and of its tail.
theorem List.allConsElim ∀ (x: a) (xs: List a) (p: a → Bool)
    (all: [x, ..xs].all p = True):
    p x = True ∧ xs.all p = True :=
  match holds: p x, all with
    | True, all => (byComputing, all)
    | False, never => (Bool.falseNotTrue never).impossible

--| A list that `isEmpty` is `[]`.
theorem List.eqNilOfIsEmpty ∀ (xs: List a) (empty: xs.isEmpty = True): xs = [] := match xs with | [] => byComputing

--| A list with an element after the front is not empty.
theorem List.isEmptyAppendCons ∀ (xs: List a) (y: a) (ys: List a): (xs ++ [y, ..ys]).isEmpty = False := match xs with
  | [] | [_, .._] => byComputing

--| Dropping the length of the first part off a join leaves the second part.
theorem List.dropAppendOf ∀ (whole read later: List t)
    (starts: whole = read ++ later):
    whole.drop read.length = later :=
  rewrite starts then List.dropAppend read later

--| `takeWhile` keeps the whole of a list whose elements all pass.
theorem List.takeWhileOfAll ∀ (passes: a → Bool) (chars: List a)
    (all: chars.all passes = True):
    chars.takeWhile passes = chars :=
  match chars with
    | [] => byComputing
    | [char, ..rest] => rewrite Bool.andLeft all, List.takeWhileOfAll passes rest (Bool.andRight all)

--| `takeWhile` over a join of a list that all passes and one that stops at once keeps the first part.
theorem List.takeWhileAppendThenStops ∀ (passes: a → Bool) (front back: List a)
    (all: front.all passes = True)
    (stops: back.takeWhile passes = []):
    (front ++ back).takeWhile passes = front :=
  match front, all with
    | [], all => stops
    | [char, ..more], all =>
      rewrite Bool.andLeft all, List.takeWhileAppendThenStops passes more back (Bool.andRight all) stops

--| Lists with the same head stop `takeWhile` together at once.
theorem List.takeWhileSameHead ∀ (passes: a → Bool) (before after: List a)
    (same: before.head = after.head)
    (stops: before.takeWhile passes = []):
    after.takeWhile passes = [] :=
  match before, after, same with
    | [], [], same => stops
    | [first, ..more], [other, ..others], same =>
      rewrite <- Option.someInjective same then
        match passes first with
          | False => byComputing

--| `takeWhile` takes nothing from a list whose head fails the test.
theorem List.takeWhileHeadFails ∀ (passes: a → Bool) (chars: List a) (first: a)
    (head: chars.head = Some first)
    (fails: passes first = False):
    chars.takeWhile passes = [] :=
  match chars, head with
    | [], head => cases
    | [other, ..more], head => rewrite Option.someInjective head, fails

--| If `takeWhile` takes nothing from a join, it takes nothing from its front.
theorem List.takeWhileNilPrefix ∀ (passes: a → Bool) (front back: List a)
    (stops: (front ++ back).takeWhile passes = []):
    front.takeWhile passes = [] :=
  match front with
    | [] => byComputing
    | [first, ..more] =>
      match pass: passes first with
        | False => byComputing

--| `takeWhile` of a list whose head passes keeps the head and goes on with the tail.
theorem List.takeWhileConsOf ∀ (passes: a → Bool) (rest: List a) (c: a) (more: List a)
    (here: rest = [c, ..more])
    (first: passes c = True):
    rest.takeWhile passes = [c, ..more.takeWhile passes] :=
  rewrite here, first

--| `dropWhile` over a join where the second part starts with an element that fails drops only from the first part.
theorem List.dropWhileAppendStop ∀ (p: a → Bool) (xs: List a) (stop: a) (more: List a)
    (stops: p stop = False):
    (xs ++ [stop, ..more]).dropWhile p = xs.dropWhile p ++ [stop, ..more] :=
  match xs with
    | [] => rewrite stops
    | [x, ..rest] =>
      match p x with
        | True => List.dropWhileAppendStop p rest stop more stops
        | False => byComputing

--| A reversed cons appended to a list is the reversed tail followed by the head and the list.
theorem List.reverseConsAppend ∀ (first: a) (rest after: List a):
    [first, ..rest].reverse ++ after = rest.reverse ++ [first, ..after] :=
  rewrite List.reverseCons first rest then List.appendAssoc rest.reverse [first] after

--| Lists related element by element are empty together.
theorem List.all2IsEmpty ∀ [r: a → b → Prop] (xs: List a) (ys: List b)
    (alike: List.All2 r xs ys):
    xs.isEmpty = ys.isEmpty :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xs], [y, ..ys] => byComputing

--| What holds of every element of a list of lists' concatenation holds of every element of every list.
theorem List.allOfConcat ∀ (p: a → Prop) (lists: List (List a))
    (all: List.All p lists.concat):
    List.All (part => List.All p part) lists :=
  match lists with
    | [] => Trivial
    | [first, ..rest] =>
      let split: List.All p (first ++ rest.concat) := all
      (
        List.allAppendLeft p first rest.concat split,
        List.allOfConcat p rest (List.allAppendRight p first rest.concat split)
      )

--| A property of a head and of a list holds of the whole list reversed, which is at least as long as the tail.
theorem List.allConsReverse ∀ (holds: a → Prop) (current: a) (found: List a) (currentHolds: holds current)
    (foundHolds: List.All holds found):
    List.All holds [current, ..found].reverse ∧ found.length + 1 <= [current, ..found].reverse.length :=
  (
    List.allReverse holds [current, ..found] (currentHolds, foundHolds),
    arithmetic [List.lengthReverse [current, ..found]]
  )

--| A test that implies another test on every element makes the second hold of whatever the first holds of.
theorem List.allImpliesBool ∀ (chars: List a) (passes follows: a → Bool)
    (implied: ∀ (char: a) => passes char = True → follows char = True)
    (all: chars.all passes = True):
    chars.all follows = True :=
  match chars, all with
    | [], all => byComputing
    | [first, ..more], all =>
      Bool.andIntro
        (implied first (Bool.andLeft all))
        (List.allImpliesBool more passes follows implied (Bool.andRight all))

--| A list with an element added at the end is not empty.
theorem List.snocNotNil ∀ (docs: List a) (last: a): docs ++ [last] ≠ [] := match docs with
  | [] => List.consNotNil last []
  | [doc, ..rest] => List.consNotNil doc (rest ++ [last])

--| Dropping fewer than all the elements leaves some.
theorem List.dropNotNil ∀ (docs: List a) (count: Nat)
    (short: count ≤ docs.length)
    (differs: (count == docs.length) = False):
    docs.drop count ≠ [] :=
  match docs, count with
    | [], Zero => cases
    | [doc, ..rest], Zero => List.consNotNil doc rest
    | [doc, ..rest], Succ more => List.dropNotNil rest more (arithmetic [short]) differs

--| Taking a positive number of elements from a non-empty list leaves some.
theorem List.takeConsNotNil ∀ (doc: a) (rest: List a) (count: Nat)
    (positive: count ≠ 0):
    [doc, ..rest].take count ≠ [] :=
  match count with
    | Zero => (positive byComputing).impossible
    | Succ more => List.consNotNil doc (rest.take more)

--| A join with two elements at the start of its second part has at least two elements.
theorem List.twoLeLengthAppend ∀ (front: List a) (first second: a) (more: List a):
    2 ≤ (front ++ [first, second, ..more]).length :=
  rewrite List.lengthAppend front [first, second, ..more] then arithmetic

--| Items related element by element to two joined lists split where the lists join.
theorem List.all2AppendSplit ∀ (r: a → b → Prop) (read: List a) (front back: List b)
    (all: List.All2 r read (front ++ back)):
    ∃ (first second: List a) => read = first ++ second ∧ List.All2 r first front ∧ List.All2 r second back :=
  match front, read, all with
    | [], read, all => ([], read, byComputing, Trivial, all)
    | [y, ..ys], [x, ..xs], (head, rest) =>
      let (first, second, isRead, firstAll, secondAll) := List.all2AppendSplit r xs ys back rest
      ([x, ..first], second, (rewrite isRead), (head, firstAll), secondAll)

--| The head of a list that starts with an element that differs from `other` is not `Some other`.
theorem List.headNeOfBeqFalse ∀ (char: Char) (more: List Char) (other: Char)
    (differs: (char == other) = False):
    [char, ..more].head ≠ Some other :=
  same => DecEq.soundFalse char other differs (Option.someInjective same)

--| The first element of a list whose head is not `Some char` is not `char`.
theorem List.beqFalseOfHeadNe ∀ (next: Char) (more: List Char) (char: Char)
    (different: [next, ..more].head ≠ Some char):
    (next == char) = False :=
  let ne: next ≠ char := same => different (rewrite same)
  DecEq.falseOfNe ne

--| The head of a list that is `Some first` is not `Some other` when `first` and `other` differ.
theorem List.headNeOfHead ∀ (rest: List Char) (first other: Char)
    (head: rest.head = Some first)
    (differs: first ≠ other):
    rest.head ≠ Some other :=
  same => differs (Option.someInjective (Eq.trans head.flipped same))

--| Where `same` implies `r`, stripping `prefix` from `xs` leaves `rest` only if
--| `xs` is some `taken` followed by `rest`, with `r` holding of each item of
--| `prefix` and the one it was compared with. [`List.stripPrefixByForward`]
--| is the case where `r` is equality.
theorem List.stripPrefixByRelated ∀ (same: a → a → Bool) (r: a → a → Prop)
    (sound: ∀ (x y: a) => same x y = True → r x y) (xs prefix: List a) [rest: List a]
    (h: List.stripPrefixBy xs prefix same = Some rest):
    ∃ (taken: List a) => xs = List.append taken rest ∧ List.All2 r prefix taken :=
  match xs, prefix with
    | xs, [] => Witness [] (Both (Option.someInjective h) Trivial)
    | [x, ..more], [p, ..ps] =>
      match holds: same p x with
        | True =>
          match List.stripPrefixByRelated same r sound more ps h with
            | Witness taken (Both split related) =>
              Witness [x, ..taken] (Both (rewrite split) (Both (sound p x holds) related))
