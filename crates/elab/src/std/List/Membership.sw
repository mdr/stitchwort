--| Lemmas about membership and distinctness: `mem` through append, map,
--| flatMap, filter, take and drop; `Distinct`; `find` and `findIndex`; and
--| `minimum`/`maximum`, with the examples and tests that use them.

theorem List.distinctNil: List.Distinct ([]: List a) := Trivial

theorem List.distinctCons ∀ (x: a) (xs: List a) (h: x ∉ xs) (d: List.Distinct xs): List.Distinct [x, ..xs] := Both h d

--| An element of two lists joined is in one of them.
theorem List.memAppend ∀ (x: a) (xs ys: List a) (h1: x ∈ List.append xs ys): (x ∈ xs) ∨ (x ∈ ys) := match xs, h1 with
  | [], h => Inr h
  | [z, ..zs], Inl h => Inl (Inl h)
  | [z, ..zs], Inr h =>
    match List.memAppend x zs ys h with
      | Inl m => Inl (Inr m)
      | Inr m => Inr m

-- And back, `List.memAppendLeft` and `List.memAppendRight`, are in the core
-- (core/Finite.sw): derived `Finite` instances use them.

theorem List.memAppendExample: 3 ∈ List.append [1, 2] [3] := List.memAppendRight 3 [1, 2] [3] (Inl byComputing)

--| `f x` is in `List.map xs f` only if `x` is in `xs`, for an injective `f`.
theorem List.memMapInjective ∀ (f: a → b)
    (inj: ∀ (x y: a) => f x = f y → x = y)
    (x: a) (xs: List a)
    (h1: f x ∈ List.map xs f):
    x ∈ xs :=
  match xs, h1 with
    | [], h => h
    | [z, ..zs], Inl h => Inl (inj z x h)
    | [z, ..zs], Inr h => Inr (List.memMapInjective f inj x zs h)

--| If `x` is in `xs`, `f x` is in `List.map xs f`.
theorem List.memMap: ∀ (xs: List a) (x: a) => x ∈ xs → ∀ (f: a → b) => f x ∈ List.map xs f
  | [], x, h, f => h
  | [z, ..zs], x, Inl h, f => Inl (Eq.cong f h)
  | [z, ..zs], x, Inr h, f => Inr (List.memMap zs x h f)

--| Use "some element satisfies `p`": take that element, know it is in the
--| list, and carry on to the goal. (The library has no `Exists`.)
theorem List.anyElim ∀ (p: a → Prop) (goal: Prop):
    ∀ (xs: List a) => List.Any p xs → ∀ (cont: ∀ (x: a) => x ∈ xs → p x → goal) => goal
  | [], h, k => h.impossible
  | [z, ..zs], Inl h, k => k z (Inl byComputing) h
  | [z, ..zs], Inr h, k => List.anyElim p goal zs h (x inZs px => k x (Inr inZs) px)

--| To prove that some element satisfies `p`, give an element of the list that does. (For the
--| `Bool` `List.any`, [`List.anyOfMem`].)
theorem List.anyIntro ∀ (p: a → Prop) (x: a) (xs: List a) (h: x ∈ xs) (px: p x): List.Any p xs := match xs, h with
  | [], m => m.impossible
  | [z, ..zs], Inl e => Inl (rewrite e then px)
  | [z, ..zs], Inr m => Inr (List.anyIntro p x zs m px)

theorem List.anyIntroExample: List.Any (n => n > 2) [1, 2, 3] :=
  List.anyIntro (n => n > 2) 3 [1, 2, 3] (Inr (Inr (Inl byComputing))) byComputing

--| What is in `List.map xs f` is `f x` for some `x` in `xs` (said with
--| `List.Any`, which also says where `x` is: `Exists` wouldn't).
theorem List.memMapAny ∀ (xs: List a) (f: a → b) (y: b) (h1: y ∈ List.map xs f): List.Any (x => f x = y) xs :=
  match xs, h1 with
    | [], h => h
    | [z, ..zs], Inl h => Inl h
    | [z, ..zs], Inr h => Inr (List.memMapAny zs f y h)

--| `List.Any` gives a member that satisfies `p`.
theorem List.anyMember ∀ (p: a → Prop) (xs: List a) (none: List.Any p xs): Exists a (x => (x ∈ xs) ∧ (p x)) :=
  match xs, none with
    | [], none => none.impossible
    | [x, ..rest], Inl here => Witness x (Both (Inl byComputing) here)
    | [x, ..rest], Inr later =>
      Exists.elim (List.anyMember p rest later) (found both => Witness found (Both (Inr both.left) both.right))

--| A member of a mapped list is the image of a member.
theorem List.memMapElim ∀ (f: a → b) (y: b) (xs: List a)
    (member: y ∈ List.map xs f):
    Exists a (x => (x ∈ xs) ∧ (f x = y)) :=
  List.anyMember (x => f x = y) xs (List.memMapAny xs f y member)

--| What `(.filter p)` keeps was in the list, and passes `p`.
theorem List.memFilter ∀ (xs: List a) (p: a → Bool) [x: a] (h: x ∈ List.filter xs p): (x ∈ xs) ∧ (p x = True) :=
  match xs with
    | [y, ..ys] =>
      match e: p y with
        | True =>
          match h with
            | Inl q => Both (Inl q) (rewrite q at e)
            | Inr m =>
              match List.memFilter ys p m with
                | Both inYs px => Both (Inr inYs) px
        | False =>
          match List.memFilter ys p h with
            | Both inYs px => Both (Inr inYs) px

--| What passes the test is kept.
theorem List.memFilterIntro ∀ (xs: List a) (p: a → Bool) [v: a] (h1: v ∈ xs) (h: p v = True): v ∈ List.filter xs p :=
  match xs, h1 with
    | [], m => m
    | [x, ..xs], Inl e => rewrite <- e at h then (rewrite h then Inl e)
    | [x, ..xs], Inr m =>
      match e: p x with
        | True => Inr (List.memFilterIntro xs p m h)
        | False => List.memFilterIntro xs p m h

--| A `filter` that keeps nothing of the list is empty.
theorem List.filterNone ∀ (p: a → Bool) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x = False): List.filter xs p = [] :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite h x (Inl byComputing) then List.filterNone p xs (y m => h y (Inr m))

--| A `filter` that keeps all of the list is the list.
theorem List.filterAll ∀ (p: a → Bool) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x = True): List.filter xs p = xs :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite h x (Inl byComputing) then Eq.cong (Cons x) (List.filterAll p xs (y m => h y (Inr m)))

--| No successor is zero, and every one is at least 1.
theorem List.filterNoneExample ∀ (xs: List Nat): List.filter (List.map xs Succ) (n => n == 0) = [] :=
  List.filterNone (n => n == 0) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) ((n == 0) = False) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e))

theorem List.filterAllExample ∀ (xs: List Nat): List.filter (List.map xs Succ) (n => Nat.leq 1 n) = List.map xs Succ :=
  List.filterAll (n => Nat.leq 1 n) (List.map xs Succ) (n m =>
    List.anyElim (x => Succ x = n) (Nat.leq 1 n = True) xs (List.memMapAny xs Succ n m) (x inXs e => rewrite <- e))

--| A list's `flatMap`: an element of `f x` for an `x` of the list is in it.
theorem List.memFlatMapIntro ∀ (f: a → List b) (x: a) (y: b) (xs: List a)
    (h1: x ∈ xs)
    (m: y ∈ f x):
    y ∈ List.flatMap xs f :=
  match xs, h1 with
    | [], h => h.impossible
    | [z, ..zs], Inl h => List.anyAppendLeft (w => w = y) (f z) (List.flatMap zs f) (rewrite h then m)
    | [z, ..zs], Inr h => List.anyAppendRight (w => w = y) (f z) (List.flatMap zs f) (List.memFlatMapIntro f x y zs h m)

--| `flatMap` over an appended list is the two `flatMap`s appended.
theorem List.flatMapAppend ∀ (f: a → List b) (first second: List a):
    List.flatMap (List.append first second) f = List.append (List.flatMap first f) (List.flatMap second f) :=
  match first with
    | [] => byComputing
    | [head, ..tail] =>
      calc List.flatMap (List.append [head, ..tail] second) f
        _ = List.append (f head) (List.append (List.flatMap tail f) (List.flatMap second f)) :=
          Eq.cong (back => List.append (f head) back) (List.flatMapAppend f tail second)
        _ = List.append (List.append (f head) (List.flatMap tail f)) (List.flatMap second f) :=
          (List.appendAssoc (f head) (List.flatMap tail f) (List.flatMap second f)).flipped

--| `flatMap` over a concatenation is the `flatMap` of each group's `flatMap`.
theorem List.flatMapConcat ∀ (f: a → List b) (groups: List (List a)):
    List.flatMap (List.concat groups) f = List.flatMap groups (group => List.flatMap group f) :=
  match groups with
    | [] => byComputing
    | [group, ..rest] =>
      calc List.flatMap (List.concat [group, ..rest]) f
        _ = List.append (List.flatMap group f) (List.flatMap (List.concat rest) f) :=
          List.flatMapAppend f group (List.concat rest)
        _ = List.append (List.flatMap group f) (List.flatMap rest (group => List.flatMap group f)) :=
          Eq.cong (back => List.append (List.flatMap group f) back) (List.flatMapConcat f rest)

--| What is in a `flatMap` is in `f x` for some `x` of the list.
theorem List.memFlatMapElim ∀ (f: a → List b) (y: b) (xs: List a)
    (h: y ∈ List.flatMap xs f):
    List.Any (x => y ∈ f x) xs :=
  match xs with
    | [z, ..zs] =>
      match List.memAppend y (f z) (List.flatMap zs f) h with
        | Inl m => Inl m
        | Inr m => Inr (List.memFlatMapElim f y zs m)

--| What is in a `flatMap` is in `f x` for some `x` of the list, and back:
--| [`List.memFlatMapIntro`] and [`List.memFlatMapElim`] as one statement, to
--| rewrite with.
theorem List.memFlatMap ∀ (f: a → List b) (y: b) (xs: List a): (y ∈ xs.flatMap f) ↔ (∃ (x: a) => x ∈ xs ∧ y ∈ f x) := {
  forward = h => List.anyMember (x => y ∈ f x) xs (List.memFlatMapElim f y xs h),
  backward = found => Exists.elim found (x both => List.memFlatMapIntro f x y xs both.left both.right)
}

--| [`List.memFlatMapIntro`] for the spelling `concat (map xs f)`.
theorem List.memConcatMapIntro ∀ (f: a → List b) (x: a) (y: b) (xs: List a)
    (inXs: x ∈ xs)
    (inF: y ∈ f x):
    y ∈ List.concat (List.map xs f) :=
  rewrite <- List.flatMapEqConcatMap f xs then List.memFlatMapIntro f x y xs inXs inF

--| [`List.memFlatMapElim`] for the spelling `concat (map xs f)`.
theorem List.memConcatMapElim ∀ (f: a → List b) (y: b) (xs: List a)
    (member: y ∈ List.concat (List.map xs f)):
    List.Any (x => y ∈ f x) xs :=
  List.memFlatMapElim f y xs (rewrite List.flatMapEqConcatMap f xs then member)

--| Mapping an injective function keeps a list distinct.
theorem List.distinctMap: ∀ (xs: List a) => List.Distinct xs
      → ∀ (f: a → b) (inj: ∀ (x y: a) => f x = f y → x = y) => List.Distinct (List.map xs f)
  | [], d, f, inj => Trivial
  | [x, ..xs], Both h d, f, inj => Both (m => h (List.memMapInjective f inj x xs m)) (List.distinctMap xs d f inj)

--| Mapping a function that is injective on the list's own members keeps the
--| list distinct; [`List.distinctMap`] needs it injective everywhere.
theorem List.distinctMapOn ∀ (f: a → b) (xs: List a)
    (h: List.Distinct xs)
    (injective: ∀ (x y: a) => x ∈ xs → y ∈ xs → f x = f y → x = y):
    List.Distinct (List.map xs f) :=
  match xs, h with
    | [], distinct => Trivial
    | [x, ..xs], Both fresh distinct =>
      Both
        (member =>
          match List.memMapElim f (f x) xs member with
            | Witness y (Both inRest same) =>
              fresh (rewrite injective x y (Inl byComputing) (Inr inRest) same.flipped then inRest))
        (List.distinctMapOn f xs distinct (first second inFirst inSecond same =>
          injective first second (Inr inFirst) (Inr inSecond) same))

--| Two distinct lists with no element in common, joined, are distinct.
theorem List.distinctAppend ∀ (xs ys: List a)
    (h: List.Distinct xs)
    (dy: List.Distinct ys)
    (h1: List.Disjoint xs ys):
    List.Distinct (List.append xs ys) :=
  match xs, h, h1 with
    | [], dx, dj => dy
    | [x, ..xs], Both hx dx, Both hj dj =>
      Both
        (m =>
          match List.memAppend x xs ys m with
            | Inl inXs => hx inXs
            | Inr inYs => hj inYs)
        (List.distinctAppend xs ys dx dy dj)

--| The parts of a list with no repeats have none, and nothing in common.
theorem List.distinctAppendLeft ∀ (xs ys: List a) (h: List.Distinct (List.append xs ys)): List.Distinct xs :=
  match xs, h with
    | [], d => Trivial
    | [x, ..rest], Both out d => Both (m => out (List.memAppendLeft x rest ys m)) (List.distinctAppendLeft rest ys d)

theorem List.distinctAppendRight ∀ (xs ys: List a) (h: List.Distinct (List.append xs ys)): List.Distinct ys :=
  match xs, h with
    | [], d => d
    | [x, ..rest], Both out d => List.distinctAppendRight rest ys d

theorem List.distinctAppendApart: ∀ (xs ys: List a) => List.Distinct (List.append xs ys)
      → ∀ (z: a) => z ∈ xs → z ∈ ys → Void
  | [], ys, d, z, inXs, inYs => inXs
  | [x, ..rest], ys, Both out d, z, Inl e, inYs => out (List.memAppendRight x rest ys (rewrite e then inYs))
  | [x, ..rest], ys, Both out d, z, Inr inRest, inYs => List.distinctAppendApart rest ys d z inRest inYs

--| Two lists with the same head are equal only if their tails are.
theorem List.consInjective ∀ (x: a) (ys zs: List a) (p: [x, ..ys] = [x, ..zs]): ys = zs := Eq.cong (.drop 1) p

--| Two equal non-empty lists have the same head: the complement of
--| [`List.consInjective`], which gives the tails when the heads are the same.
theorem List.consInjectiveHead ∀ (x y: a) (xs ys: List a) (p: [x, ..xs] = [y, ..ys]): x = y :=
  Eq.cong (list => (list.get 0).getOrElse x) p

--| Two non-empty lists are `==` when their heads are and their tails are.
theorem List.beqCons ∀ [auto eq: DecEq a] (x: a) (xs: List a) (y: a) (ys: List a):
    ([x, ..xs] == [y, ..ys]) = (x == y ∧ xs == ys) :=
  Bool.eqOf _ _
    (same =>
      let lists := DecEq.sound [x := [x, ..xs]] [y := [y, ..ys]] same
      rewrite List.consInjectiveHead x y xs ys lists, (Eq.cong (.drop 1) lists: xs = ys) then
        Both (DecEq.refl y) (DecEq.refl ys))
    (both =>
      let Both heads tails := both
      rewrite heads.read, tails.read then DecEq.refl [y, ..ys])

--| The empty list is never `==` to a non-empty one.
theorem List.beqNilCons ∀ [auto eq: DecEq a] (y: a) (ys: List a): (([]: List a) == [y, ..ys]) = False :=
  match e: (([]: List a) == [y, ..ys]) with | False => byComputing

--| A non-empty list is never `==` to the empty one.
theorem List.beqConsNil ∀ [auto eq: DecEq a] (x: a) (xs: List a): ([x, ..xs] == ([]: List a)) = False :=
  match e: ([x, ..xs] == ([]: List a)) with | False => byComputing

--| A list starting with x isn't among lists that all start with y, a
--| different element.
theorem List.notMemMapCons ∀ (x y: a) (ne: x ≠ y) (xs: List a) (ys: List (List a)): [x, ..xs] ∉ List.map ys (Cons y) :=
  match ys with
    | [] => m => m
    | [z, ..zs] =>
      match
        | Inl p => ne (Eq.flipped (Eq.cong (.headOr x) p))
        | Inr q => List.notMemMapCons x y ne xs zs q

--| Lists that all start with x and lists that all start with a different y
--| have none in common.
theorem List.disjointMapCons ∀ (ys: List (List a)) (x y: a)
    (ne: x ≠ y) (xs: List (List a)):
    List.Disjoint (List.map xs (Cons x)) (List.map ys (Cons y)) :=
  match xs with
    | [] => Trivial
    | [z, ..zs] => Both (List.notMemMapCons x y ne z ys) (List.disjointMapCons ys x y ne zs)

--| A run of numbers has no repeats.
theorem List.distinctRangeFrom ∀ (c s: Nat): List.Distinct (List.rangeFrom c s) := match c with
  | Zero => Trivial
  | Succ c =>
    Both
      (m =>
        match List.memRangeFrom s c (Succ s) m with
          | Both above _ => Nat.lessIrrefl s above)
      (List.distinctRangeFrom c (Succ s))

--| A range has no repeats.
theorem List.distinctRange ∀ (a b: Nat): List.Distinct (List.range a b) := List.distinctRangeFrom (b - a) a

--| Every element of the list passes, given that each element that is in it does.
theorem List.allOfMem ∀ (p: a → Prop) (xs: List a) (h: ∀ (x: a) => x ∈ xs → p x): List.All p xs := match xs with
  | [] => Trivial
  | [z, ..zs] => Both (h z (Inl byComputing)) (List.allOfMem p zs (x inZs => h x (Inr inZs)))

--| A `flatMap` of distinct lists has no repeats if the list mapped over has none
--| and the lists apart: `key` says which element of `xs` each result came from.
theorem List.distinctFlatMap ∀ (f: a → List b) (key: b → a) (xs: List a)
    (d: List.Distinct xs)
    (distinctEach: ∀ (x: a) => x ∈ xs → List.Distinct (f x))
    (keyed: ∀ (x: a) => x ∈ xs → ∀ (y: b) => y ∈ f x → key y = x):
    List.Distinct (List.flatMap xs f) :=
  match xs, d with
    | [], d => Trivial
    | [x, ..xs], Both notLater later =>
      List.distinctAppend
        (f x)
        (List.flatMap xs f)
        (distinctEach x (Inl byComputing))
        (List.distinctFlatMap f key xs later (z inXs => distinctEach z (Inr inXs)) (z inXs => keyed z (Inr inXs)))
        -- Nothing in `f x` is in a later `f z`: it would have key `x` and key `z`.
        (List.allOfMem (y => y ∉ List.flatMap xs f) (f x) (y fromX inLater =>
          List.anyElim (z => y ∈ f z) Void xs (List.memFlatMapElim f y xs inLater) (z inXs fromZ =>
            notLater
              (rewrite Eq.trans (Eq.flipped (keyed x (Inl byComputing) y fromX)) (keyed z (Inr inXs) y fromZ) then
                inXs))))

--| [`List.distinctFlatMap`] for the spelling `concat (map xs f)`.
theorem List.distinctConcatMap ∀ (f: a → List b) (key: b → a) (xs: List a)
    (distinct: List.Distinct xs)
    (distinctEach: ∀ (x: a) => x ∈ xs → List.Distinct (f x))
    (keyed: ∀ (x: a) => x ∈ xs → ∀ (y: b) => y ∈ f x → key y = x):
    List.Distinct (List.concat (List.map xs f)) :=
  rewrite <- List.flatMapEqConcatMap f xs then List.distinctFlatMap f key xs distinct distinctEach keyed

--| A member of a list splits it around that occurrence:
--| `[1, 2, 3]` is `[1] ++ [2, ..[3]]` for the 2.
theorem List.memSplit ∀ (x: a) (xs: List a)
    (member: x ∈ xs):
    ∃ (before: List a) => ∃ (after: List a) => xs = before ++ [x, ..after] :=
  match xs, member with
    | [], member => member.impossible
    | [z, ..zs], Inl same => Witness [] (Witness zs (rewrite same))
    | [z, ..zs], Inr later =>
      match List.memSplit x zs later with
        | Witness before (Witness after eq) => Witness [z, ..before] (Witness after (Eq.cong (Cons z) eq))

--| A list with no repeats whose elements are all in `ys` is no longer than
--| `ys` (`ys` itself may repeat). The pigeonhole principle for lists is
--| [`List.pigeonhole`].
theorem List.distinctLength ∀ [auto eq: DecEq a] (xs ys: List a)
    (h: List.Distinct xs)
    (drawn: ∀ (x: a) => x ∈ xs → x ∈ ys):
    List.length xs ≤ List.length ys :=
  match xs, h with
    | [], d => Nat.zeroLe (List.length ys)
    | [x, ..rest], Both out d =>
      let others := ys.filter (y => Bool.not (y == x))
      let dropped: Bool.not (x == x) = False := rewrite DecEq.refl x
      let drawnOthers: ∀ (y: a) => y ∈ rest → y ∈ others := y inRest =>
        List.memFilterIntro ys
          (y => Bool.not (y == x))
          (drawn y (Inr inRest))
          (match e: y == x with
            | True => Void.impossible (out (rewrite <- e.read then inRest))
            | False => byComputing)
      arithmetic [
        List.distinctLength rest others d drawnOthers,
        List.lengthFilterLt (y => Bool.not (y == x)) x dropped ys (drawn x (Inl byComputing))
      ]

--| The pigeonhole principle for lists: if every element of `xs` is one of
--| the elements of `ys`, and `xs` is longer than `ys`, then `xs` repeats an
--| element, that is, it is not [`List.Distinct`]. `ys` may itself have
--| repeats, so its length is an upper bound on the distinct values: a path
--| of more steps than a graph has nodes passes through one twice.
--|
--| `¬List.Distinct xs` is the form to use when the repeat only has to be
--| known to exist; [`List.repeatSplit`] turns it into the two positions,
--| for an argument that cuts the repeated stretch out or repeats it. For
--| example ([`List.pigeonholeExample`]), `[1, 2, 1]` is drawn from `[1, 2]`
--| and longer, so it repeats.
theorem List.pigeonhole ∀ [auto eq: DecEq a] (xs ys: List a)
    (drawn: ∀ (x: a) => x ∈ xs → x ∈ ys)
    (shorter: List.length ys < List.length xs):
    ¬List.Distinct xs :=
  d => arithmetic [List.distinctLength xs ys d drawn]

--| A list that is not [`List.Distinct`] has some element twice: it is
--| `before`, then the element, then `between`, then the element again, then
--| `after`, as `[1, 2, 1]` is `[] ++ [1, ..([2] ++ [1, ..[]])]`. Cutting
--| out `between` and one copy of the element, or repeating them, keeps the
--| list's neighbours the same, which a walk that revisits a node needs.
theorem List.repeatSplit ∀ [auto eq: DecEq a] (xs: List a)
    (notDistinct: ¬List.Distinct xs):
    ∃ (before: List a) => ∃ (x: a) => ∃ (between: List a) => ∃ (after: List a) => xs
      = before ++ [x, ..(between ++ [x, ..after])] :=
  match xs with
    | [] => (notDistinct Trivial).impossible
    | [y, ..rest] =>
      if found: y ∈ rest then
        match List.memSplit y rest found with
          | Witness between (Witness after eq) =>
            Witness [] (Witness y (Witness between (Witness after (Eq.cong (Cons y) eq))))
      else
        match List.repeatSplit rest (d => notDistinct (Both found d)) with
          | Witness before (Witness x (Witness between (Witness after eq))) =>
            Witness [y, ..before] (Witness x (Witness between (Witness after (Eq.cong (Cons y) eq))))

theorem List.pigeonholeExample: ¬List.Distinct [1, 2, 1] :=
  List.pigeonhole
    [1, 2, 1]
    [1, 2]
    (x m =>
      match m with
        | Inl p => Inl p
        | Inr (Inl p) => Inr (Inl p)
        | Inr (Inr (Inl p)) => Inl p
        | Inr (Inr (Inr v)) => v.impossible)
    byDecision

theorem List.distinctExample: List.Distinct [1, 2] :=
  Both
    (m =>
      match m with
        | Inl p => Nat.succNotZero 0 (Nat.succInjective p)
        | Inr v => v)
    (Both (m => m) Trivial)

theorem List.distinctMapExample: List.Distinct (List.map [1, 2] Succ) :=
  List.distinctMap [1, 2] List.distinctExample Succ (x y p => Nat.succInjective p)

theorem List.consInjectiveExample ∀ (ys zs: List Nat) (p: [1, ..ys] = [1, ..zs]): ys = zs :=
  List.consInjective 1 ys zs p

theorem List.disjointMapConsExample: List.Disjoint (List.map [[1], [2]] (Cons 0)) (List.map [[1], []] (Cons 1)) :=
  List.disjointMapCons [[1], []] 0 1 (p => Nat.succNotZero 0 p.flipped) [[1], [2]]

theorem List.distinctMapConsExample: List.Distinct (List.append (List.map [[]] (Cons 0)) (List.map [[]] (Cons 1))) :=
  List.distinctAppend
    (List.map [[]] (Cons 0))
    (List.map [[]] (Cons 1))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 0) (List.consInjective 0))
    (List.distinctMap [[]] (Both (m => m) Trivial) (Cons 1) (List.consInjective 1))
    (List.disjointMapCons [[]] 0 1 (p => Nat.succNotZero 0 p.flipped) [[]])

--| `x` is in `List.range a b` exactly when `a ≤ x < b`.
theorem List.memRange ∀ (x a b: Nat): x ∈ List.range a b ↔ (a ≤ x < b) :=
  { forward = List.memRangeBounds x a b, backward = List.memRangeOf x a b }

--| `List.inRange x a b` holds exactly when `x ∈ a ..< b`.
theorem List.inRangeIff ∀ (x a b: Nat): (List.inRange x a b = True) ↔ (x ∈ List.range a b) := {
  forward = h => (List.memRange x a b).backward arithmetic,
  backward = m =>
    let bounds := (List.memRange x a b).forward m
    arithmetic
}

--| Looking for `x` in a range with `contains` gives the two comparisons `x in a ..< b` is.
theorem List.containsRange ∀ (a b x: Nat): List.contains (List.range a b) x = List.inRange x a b :=
  match c: List.contains (List.range a b) x with
    | True => Eq.flipped ((List.inRangeIff x a b).backward c.read)
    | False =>
      match d: List.inRange x a b with
        | True =>
          Void.impossible
            (Bool.trueNotFalse
              (Eq.trans
                (Eq.flipped ((List.memContains (List.range a b) x).backward ((List.inRangeIff x a b).forward d)))
                c))
        | False => byComputing

theorem List.memRangeExample: 3 ∈ List.range 1 6 := (List.memRange 3 1 6).backward (Both byComputing byComputing)

theorem List.memFlatMapExample: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10]) :=
  List.memFlatMapIntro (x => [x, x * 10]) 2 20 [1, 2] (Inr (Inl byComputing)) (Inr (Inl byComputing))

theorem List.memFlatMapExample2: 20 ∈ List.flatMap [1, 2] (x => [x, x * 10])
      ↔ (∃ (x: Nat) => x ∈ [1, 2] ∧ 20 ∈ [x, x * 10]) :=
  List.memFlatMap (x => [x, x * 10]) 20 [1, 2]

theorem List.distinctAppendExample: List.Distinct (List.append [1] [2]) :=
  List.distinctAppend
    [1]
    [2]
    (Both (m => m) Trivial)
    (Both (m => m) Trivial)
    (Both
      (m =>
        match m with
          | Inl p => Nat.succNotZero 0 (Nat.succInjective p)
          | Inr v => v)
      Trivial)

--| What `List.All` says of an element of the list.
theorem List.allMem ∀ (p: a → Prop) (x: a) (xs: List a) (h1: List.All p xs) (h2: x ∈ xs): p x := match xs, h1, h2 with
  | [], h, m => m.impossible
  | [z, ..zs], Both pz h, Inl e => rewrite <- e then pz
  | [z, ..zs], Both pz h, Inr m => List.allMem p x zs h m

-- `List.find` and `List.any`, and keys that are distinct (SW-363): lemmas
-- for code that finds records by an id.

--| What `List.find` finds passes the test and is in the list.
theorem List.findSome ∀ (xs: List a) (p: a → Bool) (y: a) (h: List.find xs p = Some y): (p y = True) ∧ (y ∈ xs) :=
  match xs with
    | [x, ..xs] =>
      match e: p x with
        | True => Both (Eq.trans (Eq.cong p (Option.someInjective h).flipped) e) (Inl (Option.someInjective h))
        | False =>
          match List.findSome xs p y h with
            | Both py m => Both py (Inr m)

--| `List.find` finds nothing only when no element passes.
theorem List.findNoneNotMem ∀ (xs: List a) (p: a → Bool) (x: a)
    (px: p x = True)
    (h1: x ∈ xs)
    (h: List.find xs p = None):
    Void :=
  match xs, h1 with
    | [], m => m
    | [z, ..zs], Inl e => Option.someNotNone x (rewrite e, px at h)
    | [z, ..zs], Inr m =>
      match c: p z with
        | False => List.findNoneNotMem zs p x px m h

--| Finding nothing means every element fails, as an `all`. So
--| `find xs bad = None` gives `xs.all (x => ¬(bad x))`, and a search for
--| one that isn't `good` finding nothing gives `xs.all good`.
theorem List.findNoneAll ∀ (xs: List a) (p: a → Bool) (h: List.find xs p = None): List.all xs (x => ¬(p x)) = True :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findNoneAll rest p h

theorem List.findNotNoneAll ∀ (xs: List a) (good: a → Bool)
    (h: List.find xs (x => ¬(good x)) = None):
    List.all xs good = True :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: good x with
        | True => List.findNotNoneAll rest good h

--| Searching the elements paired with their indices (`withIndex`) by the
--| element alone finds nothing exactly when searching the list does.
theorem List.findWithIndexFromNone ∀ (p: a → Bool) (i: Nat) (xs: List a)
    (h: List.find (List.withIndexFrom i xs) (((_, x)) => p x) = None):
    List.find xs p = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findWithIndexFromNone p (Succ i) rest h

--| Searching the elements paired with their indices by the element alone finds
--| nothing when searching the list does ([`List.findWithIndexFromNone`] the
--| other way).
theorem List.findNoneWithIndexFrom ∀ (p: a → Bool) (i: Nat) (xs: List a)
    (h: List.find xs p = None):
    List.find (List.withIndexFrom i xs) (((_, x)) => p x) = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      match e: p x with
        | False => List.findNoneWithIndexFrom p (Succ i) rest h

--| `List.find` finds nothing when no element passes ([`List.findNoneNotMem`]
--| the other way).
theorem List.findNoneOfMem ∀ (p: a → Bool) (xs: List a)
    (fails: ∀ (x: a) => x ∈ xs → p x = False):
    List.find xs p = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite fails x (Inl byComputing) then List.findNoneOfMem p rest (y member => fails y (Inr member))

-- `List.find` over `List.range`: what it finds is the least number that
-- passes, and when it finds nothing, no number in the range passes.

--| No number from `start` up to the one found passes.
theorem List.findRangeFirst ∀ (passes: Nat → Bool):
    ∀ (count start found: Nat) => (List.rangeFrom count start).find passes = Some found
      → ∀ (earlier: Nat) => start ≤ earlier → earlier < found → passes earlier = False
  | Zero, start, found, h, earlier, low, high => (Option.noneNotSome found h).impossible
  | Succ count, start, found, h, earlier, low, high =>
    match c: passes start with
      | True =>
        let same: start = found := Option.someInjective h
        Void.impossible
          (Nat.lessIrrefl earlier (Nat.leTrans (Succ earlier) found earlier high (rewrite <- same then low)))
      | False =>
        match e: earlier == start with
          | True => rewrite e.read then c
          | False =>
            let later: Succ start ≤ earlier := Nat.leNeSucc start earlier low (p => e.read p.flipped)
            List.findRangeFirst passes count (Succ start) found h earlier later high

--| What is found passes, is in the range, and no smaller number passes.
theorem List.findRangeSome ∀ (passes: Nat → Bool) (count found: Nat)
    (h: (List.range 0 count).find passes = Some found):
    (passes found = True) ∧ ((found < count) ∧ (∀ (earlier: Nat) => earlier < found → passes earlier = False)) :=
  match List.findSome (List.range 0 count) passes found h with
    | Both foundPasses member =>
      Both foundPasses
        (Both (And.right (List.memRangeFrom found count 0 member)) (earlier before =>
          List.findRangeFirst passes count 0 found h earlier (Nat.zeroLe earlier) before))

--| Finding nothing means no number in the range passes.
theorem List.findRangeNone ∀ (passes: Nat → Bool) (count: Nat)
    (h: (List.range 0 count).find passes = None) (n: Nat)
    (below: n < count):
    passes n = False :=
  match c: passes n with
    | True =>
      Void.impossible
        (List.findNoneNotMem (List.range 0 count) passes n c (List.memRangeFromIntro n count 0 (Nat.zeroLe n) below) h)
    | False => byComputing

test "List.findRangeSome" := List.range 0 10 |> .find (n => n * n > 20) == Some 5

-- `List.findIndex`: what the first index that passes is, in the form that
-- carries the induction, `findIndexFrom` (a cons step moves its start).

--| A step of [`List.findIndexFromSome`]: when `x` fails `p` and nothing in
--| `rest` from `start + 1` up to `index` passes, nothing in `[x, ..rest]`
--| from `start` up to `index` does.
theorem List.findIndexFromSomeBefore ∀ (p: a → Bool) (x: a) (rest: List a) (start index: Nat)
    (e: p x = False)
    (before: ∀ (earlier: Nat) => Succ start ≤ earlier
      → earlier < index
      → ∀ (y: a) => rest.get (earlier - Succ start) = Some y → p y = False):
    ∀ (earlier: Nat) => start ≤ earlier
      → earlier < index
      → ∀ (y: a) => [x, ..rest].get (earlier - start) = Some y → p y = False :=
  earlier lo2 hi y g =>
    match same: earlier == start with
      | True =>
        let zero: earlier - start = 0 := arithmetic [same]
        rewrite <- Option.someInjective (rewrite zero at g then g) then e
      | False =>
        let ne: earlier ≠ start := same.read
        let later: Succ start ≤ earlier := arithmetic
        let shift2: earlier - start = Succ (earlier - Succ start) := arithmetic
        before earlier later hi y (rewrite shift2 at g then g)

--| What `findIndexFrom` finds passes, and nothing before it does.
theorem List.findIndexFromSome ∀ (p: a → Bool) (start: Nat) (xs: List a) (index: Nat)
    (h: List.findIndexFrom start p xs = Some index):
    (start ≤ index)
      ∧ (∃ (x: a) => (xs.get (index - start) = Some x) ∧ (p x = True))
      ∧ (∀ (earlier: Nat) => start ≤ earlier
        → earlier < index
        → ∀ (y: a) => xs.get (earlier - start) = Some y → p y = False) :=
  match xs with
    | [x, ..rest] =>
      match e: p x with
        | True =>
          let isStart: start = index := Option.someInjective h
          let zero: index - start = 0 := arithmetic
          Both
            (Nat.leOfEq start index isStart)
            (Both (Witness x (rewrite zero then Both byComputing e)) (earlier lo hi y g =>
              let impossible: earlier < earlier := arithmetic
              Void.impossible (Nat.lessIrrefl earlier impossible)))
        | False =>
          let (Both lo (Both there before)) := List.findIndexFromSome p (Succ start) rest index h
          let shift: index - start = Succ (index - Succ start) := arithmetic
          let ok: start ≤ index := arithmetic
          Both ok
            (Both
              (Exists.elim there (w both => Witness w (Both (rewrite shift then both.left) both.right)))
              (List.findIndexFromSomeBefore p x rest start index e before))

--| What `findIndexFrom` does not find: no member passes.
theorem List.findIndexFromNone ∀ (p: a → Bool):
    ∀ (start: Nat) (xs: List a) => List.findIndexFrom start p xs = None → ∀ (x: a) => x ∈ xs → p x = False
  | start, [], h, x, member => member.impossible
  | start, [z, ..rest], h, x, member =>
    match e: p z with
      | False =>
        match member with
          | Inl isZ => rewrite <- isZ then e
          | Inr later => List.findIndexFromNone p (Succ start) rest h x later

--| The first index that passes is what `findIndexFrom` finds.
theorem List.findIndexFromOf ∀ (p: a → Bool) (start: Nat) (xs: List a) (index: Nat) (x: a)
    (lo: start ≤ index)
    (g: xs.get (index - start) = Some x)
    (passes: p x = True)
    (before: ∀ (earlier: Nat) => start ≤ earlier
      → earlier < index
      → ∀ (y: a) => xs.get (earlier - start) = Some y → p y = False):
    List.findIndexFrom start p xs = Some index :=
  match xs with
    | [z, ..rest] =>
      match e: p z with
        | True =>
          match same: index == start with
            | True => rewrite same.read
            | False =>
              let ne: index ≠ start := same.read
              let less: start < index := arithmetic
              let zero: start - start = 0 := arithmetic
              Void.impossible
                (Bool.falseNotTrue (Eq.trans (Eq.flipped (before start (Nat.leRefl start) less z (rewrite zero))) e))
        | False =>
          match same: index == start with
            | True =>
              let zero: index - start = 0 := arithmetic [same]
              let isZ: z = x := Option.someInjective (rewrite zero at g then g)
              Void.impossible (Bool.falseNotTrue (Eq.trans e.flipped (rewrite isZ then passes)))
            | False =>
              let ne: index ≠ start := same.read
              let later: Succ start ≤ index := arithmetic
              let shift: index - start = Succ (index - Succ start) := arithmetic
              List.findIndexFromOf p
                (Succ start)
                rest
                index
                x
                later
                (rewrite shift at g then g)
                passes
                (earlier lo2 hi y g2 =>
                  let shift2: earlier - start = Succ (earlier - Succ start) := arithmetic
                  before earlier
                    (Nat.leTrans start (Succ start) earlier (Nat.leSucc start) lo2)
                    hi
                    y
                    (rewrite shift2 then g2))

--| What `findIndex` finds passes, and nothing before it does.
theorem List.findIndexSome ∀ (xs: List a) (p: a → Bool) (index: Nat)
    (found: xs.findIndex p = Some index):
    (∃ (x: a) => (xs.get index = Some x) ∧ (p x = True))
      ∧ (∀ (earlier: Nat) => earlier < index → ∀ (y: a) => xs.get earlier = Some y → p y = False) :=
  let (Both lo (Both there before)) := List.findIndexFromSome p 0 xs index found
  let zero: index - 0 = index := arithmetic
  Both (rewrite zero at there then there) (earlier below y g =>
    let zero2: earlier - 0 = earlier := arithmetic
    before earlier (Nat.zeroLe earlier) below y (rewrite zero2 then g))

--| `findIndex` finds nothing only if no member passes.
theorem List.findIndexNone ∀ (xs: List a) (p: a → Bool)
    (found: xs.findIndex p = None) (x: a)
    (member: x ∈ xs):
    p x = False :=
  List.findIndexFromNone p 0 xs found x member

--| The first index that passes is what `findIndex` finds.
theorem List.findIndexOf ∀ (xs: List a) (p: a → Bool) (index: Nat) (x: a)
    (at: xs.get index = Some x)
    (passes: p x = True)
    (before: ∀ (earlier: Nat) => earlier < index → ∀ (y: a) => xs.get earlier = Some y → p y = False):
    xs.findIndex p = Some index :=
  let zero: index - 0 = index := arithmetic
  List.findIndexFromOf p 0 xs index x (Nat.zeroLe index) (rewrite zero then at) passes (earlier lo below y g =>
    let zero2: earlier - 0 = earlier := arithmetic
    before earlier below y (rewrite zero2 at g then g))

test "List.findIndexSome" :=
  let xs := [5, 6, 7, 8]
  xs.findIndex (x => Nat.leq 7 x) == Some 2 ∧ xs.get 2 == Some 7 ∧ xs.findIndex (x => Nat.leq 9 x) == None

-- `List.minimum`: the least of a list that holds `least` and nothing else
-- is `least`, an empty list has none, and what it finds is in the list and
-- at most each element.

--| Folding `Ord.min` from `least` over elements that are all `least`.
theorem List.foldMinAll ∀ [auto ord: Ord a] (least: a) (xs: List a)
    (all: ∀ (x: a) => x ∈ xs → x = least):
    List.foldLeft xs least Ord.min = least :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite all x (Inl byComputing), Ord.minSelf least then
        List.foldMinAll least rest (y member => all y (Inr member))

theorem List.minimumAllEqual ∀ [auto ord: Ord a] (least: a) (xs: List a)
    (member: least ∈ xs)
    (all: ∀ (x: a) => x ∈ xs → x = least):
    List.minimum xs = Some least :=
  match xs with
    | [x, ..rest] =>
      rewrite all x (Inl byComputing) then Eq.cong Some (List.foldMinAll least rest (y member => all y (Inr member)))

theorem List.minimumEmpty ∀ [auto ord: Ord a] (xs: List a) (none: ∀ (x: a) => x ∈ xs → Void): List.minimum xs = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => Void.impossible (none x (Inl byComputing))

--| Folding with `Ord.min` gives at most the start and each element, and
--| gives the start or an element.
theorem List.foldMinLeStart ∀ [auto ord: Ord a] (xs: List a) (start: a): List.foldLeft xs start Ord.min <= start :=
  match xs with
    | [] => Ord.leRefl start
    | [y, ..ys] =>
      Ord.leTrans
        (List.foldLeft ys (Ord.min start y) Ord.min)
        (Ord.min start y)
        start
        (List.foldMinLeStart ys (Ord.min start y))
        (Ord.minLeLeft start y)

theorem List.foldMinLeMember ∀ [auto ord: Ord a] (xs: List a) (start x: a)
    (h: x ∈ xs):
    List.foldLeft xs start Ord.min <= x :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        Ord.leTrans
          (List.foldLeft ys (Ord.min start y) Ord.min)
          (Ord.min start y)
          y
          (List.foldMinLeStart ys (Ord.min start y))
          (Ord.minLeRight start y)
    | [y, ..ys], Inr member => List.foldMinLeMember ys (Ord.min start y) x member

theorem List.foldMinMember ∀ [auto ord: Ord a] (xs: List a) (start: a):
    (List.foldLeft xs start Ord.min = start) ∨ (List.foldLeft xs start Ord.min ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match List.foldMinMember ys (Ord.min start y) with
        | Inr member => Inr (Inr member)
        | Inl same =>
          match Ord.minEither start y with
            | Inl isStart => Inl (Eq.trans same isStart)
            | Inr isY => Inr (Inl (Eq.trans same isY).flipped)

--| The least element is in the list and at most every element.
theorem List.minimumSome ∀ [auto ord: Ord a] (xs: List a) (least: a)
    (found: List.minimum xs = Some least):
    (least ∈ xs) ∧ (∀ (x: a) => x ∈ xs → least <= x) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMinMember ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMinLeStart ys y
              | Inr inRest => List.foldMinLeMember ys y x inRest)

--| A list with an element has a least one.
theorem List.minimumExists ∀ [auto ord: Ord a] (xs: List a) (x: a)
    (member: x ∈ xs):
    ∃ (least: a) => List.minimum xs = Some least :=
  match xs with | [y, ..ys] => Witness (List.foldLeft ys y Ord.min) byComputing

--| A list with an element has a least one: `List.minimum` isn't `None`.
theorem List.minimumNone ∀ [auto ord: Ord a] (xs: List a)
    (none: List.minimum xs = None) (x: a)
    (member: x ∈ xs):
    Void :=
  match xs with | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.min) none

--| Lists with the same members have the same least member.
theorem List.minimumSameMembers ∀ [auto ord: Ord a] (xs ys: List a)
    (into: ∀ (v: a) => v ∈ xs → v ∈ ys)
    (back: ∀ (v: a) => v ∈ ys → v ∈ xs):
    List.minimum xs = List.minimum ys :=
  match mx: List.minimum xs with
    | None =>
      match my: List.minimum ys with
        | None => byComputing
        | Some y => Void.impossible (List.minimumNone xs mx y (back y (List.minimumSome ys y my).left))
    | Some x =>
      match my: List.minimum ys with
        | None => Void.impossible (List.minimumNone ys my x (into x (List.minimumSome xs x mx).left))
        | Some y =>
          let (Both xIn xLeast) := List.minimumSome xs x mx
          let (Both yIn yLeast) := List.minimumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (xLeast y (back y yIn)) (yLeast x (into x xIn)))

-- `List.minBy`: the result is a member, its key is at most every member's,
-- and no member before it has a key as small (the first of the smallest wins).

--| Folding with `List.minByStep` gives a key at most the start's, and the
--| start or a member.
theorem List.foldMinByLeStart ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    f (List.foldLeft xs start (List.minByStep f)) <= f start :=
  match xs with
    | [] => Ord.leRefl (f start)
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          let flipped: Ord.compare (f y) (f start) = Less := rewrite order at ord.flip (f start) (f y)
          Ord.leTrans
            (f (List.foldLeft ys y (List.minByStep f)))
            (f y)
            (f start)
            (List.foldMinByLeStart f ys y)
            (Ord.lessLe (f y) (f start) (ord.lessThanOf (f y) (f start) flipped))
        | Less | Equal => List.foldMinByLeStart f ys start

--| Folding with `List.minByStep` gives a key at most each member's.
theorem List.foldMinByLeMember ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start x: a)
    (h: x ∈ xs):
    f (List.foldLeft xs start (List.minByStep f)) <= f x :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        match order: Ord.compare (f start) (f y) with
          | Greater => List.foldMinByLeStart f ys y
          | Less =>
            Ord.leTrans
              (f (List.foldLeft ys start (List.minByStep f)))
              (f start)
              (f y)
              (List.foldMinByLeStart f ys start)
              (ord.lessEqOf (f start) (f y) (greater => Ordering.lessNotGreater (Eq.trans order.flipped greater)))
          | Equal =>
            Ord.leTrans
              (f (List.foldLeft ys start (List.minByStep f)))
              (f start)
              (f y)
              (List.foldMinByLeStart f ys start)
              (ord.lessEqOf (f start) (f y) (greater => Ordering.equalNotGreater (Eq.trans order.flipped greater)))
    | [y, ..ys], Inr member =>
      match order: Ord.compare (f start) (f y) with
        | Greater => List.foldMinByLeMember f ys y x member
        | Less | Equal => List.foldMinByLeMember f ys start x member

--| Folding with `List.minByStep` gives the start or a member.
theorem List.foldMinByMember ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    (List.foldLeft xs start (List.minByStep f) = start) ∨ (List.foldLeft xs start (List.minByStep f) ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          match List.foldMinByMember f ys y with
            | Inl same => Inr (Inl same.flipped)
            | Inr member => Inr (Inr member)
        | Less | Equal =>
          match List.foldMinByMember f ys start with
            | Inl same => Inl same
            | Inr member => Inr (Inr member)

--| The case of [`List.foldMinByFirst`] where the start is kept over `y`: given
--| the split for `start :: ys`, which leaves `y` out, `y` goes after the start.
theorem List.foldMinByFirstKeep ∀ [auto ord: Ord b] (f: a → b) (ys: List a) (start y: a)
    (kept: f start <= f y)
    (split: ∃ (before: List a) => ∃ (after: List a) => ([start, ..ys]
      = before ++ [List.foldLeft ys start (List.minByStep f), ..after])
      ∧ (∀ (z: a) => z ∈ before → f (List.foldLeft ys start (List.minByStep f)) < f z)):
    ∃ (before: List a) => ∃ (after: List a) => ([start, y, ..ys]
      = before ++ [List.foldLeft ys start (List.minByStep f), ..after])
      ∧ (∀ (z: a) => z ∈ before → f (List.foldLeft ys start (List.minByStep f)) < f z) :=
  match split with
    | Witness [] (Witness after (Both same earlier)) =>
      let isStart: start = List.foldLeft ys start (List.minByStep f) := List.consInjectiveHead start _ ys after same
      Witness [] (Witness [y, ..ys] (Both (rewrite <- isStart) (z member => member.impossible)))
    | Witness [c, ..before] (Witness after (Both same earlier)) =>
      let isStart: start = c :=
        List.consInjectiveHead start c ys (before ++ [List.foldLeft ys start (List.minByStep f), ..after]) same
      let rest: ys = before ++ [List.foldLeft ys start (List.minByStep f), ..after] := Eq.cong (.drop 1) same
      let belowStart: f (List.foldLeft ys start (List.minByStep f)) < f start :=
        rewrite <- isStart at (earlier c (Inl byComputing))
      Witness
        [start, y, ..before]
        (Witness after
          (Both (Eq.cong (t => [start, y, ..t]) rest) (z member =>
            match member with
              | Inl same => rewrite <- same then belowStart
              | Inr (Inl same) =>
                rewrite <- same then
                  Ord.lessLeTrans (f (List.foldLeft ys start (List.minByStep f))) (f start) (f y) belowStart kept
              | Inr (Inr inBefore) => earlier z (Inr inBefore))))

--| The result of folding with `List.minByStep` from `start` over `xs` is the
--| first element of `start :: xs` whose key is the smallest: the list splits
--| around it, and every element before it has a strictly larger key.
theorem List.foldMinByFirst ∀ [auto ord: Ord b] (f: a → b) (xs: List a) (start: a):
    ∃ (before: List a) => ∃ (after: List a) => ([start, ..xs]
      = before ++ [List.foldLeft xs start (List.minByStep f), ..after])
      ∧ (∀ (y: a) => y ∈ before → f (List.foldLeft xs start (List.minByStep f)) < f y) :=
  match xs with
    | [] => Witness [] (Witness [] (Both byComputing (y member => member.impossible)))
    | [y, ..ys] =>
      match order: Ord.compare (f start) (f y) with
        | Greater =>
          let flipped: Ord.compare (f y) (f start) = Less := rewrite order at ord.flip (f start) (f y)
          let startAbove: f y < f start := ord.lessThanOf (f y) (f start) flipped
          match List.foldMinByFirst f ys y with
            | Witness before (Witness after (Both split earlier)) =>
              -- Bound here, not written inline: the inline lambda is checked inside
              -- three constructor arguments, which a debug build's stack budget
              -- doesn't allow.
              let below: ∀ (z: a) => z ∈ [start, ..before] → f (List.foldLeft ys y (List.minByStep f)) < f z :=
                z member =>
                  match member with
                    | Inl same =>
                      rewrite <- same then
                        Ord.leLessTrans
                          (f (List.foldLeft ys y (List.minByStep f)))
                          (f y)
                          (f start)
                          (List.foldMinByLeStart f ys y)
                          startAbove
                    | Inr inBefore => earlier z inBefore
              Witness [start, ..before] (Witness after (Both (rewrite split) below))
        | Less =>
          List.foldMinByFirstKeep f ys start y
            (ord.lessEqOf (f start) (f y) (greater => Ordering.lessNotGreater (Eq.trans order.flipped greater)))
            (List.foldMinByFirst f ys start)
        | Equal =>
          List.foldMinByFirstKeep f ys start y
            (ord.lessEqOf (f start) (f y) (greater => Ordering.equalNotGreater (Eq.trans order.flipped greater)))
            (List.foldMinByFirst f ys start)

--| `List.minBy` finds a member, and its key is at most every member's.
theorem List.minBySome ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (least: a)
    (found: List.minBy xs f = Some least):
    (least ∈ xs) ∧ (∀ (x: a) => x ∈ xs → f least <= f x) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMinByMember f ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMinByLeStart f ys y
              | Inr inRest => List.foldMinByLeMember f ys y x inRest)

--| `minBy` finds nothing only in an empty list.
theorem List.minByNone ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (found: List.minBy xs f = None): xs = [] :=
  match xs with | [] => byComputing

--| `List.minBy` finds the FIRST element with the smallest key: the list
--| splits around the result, and every element before it has a strictly
--| larger key.
theorem List.minByFirst ∀ [auto ord: Ord b] (xs: List a) (f: a → b) (least: a)
    (found: List.minBy xs f = Some least):
    ∃ (before: List a) => ∃ (after: List a) => (xs = before ++ [least, ..after])
      ∧ (∀ (x: a) => x ∈ before → f least < f x) :=
  match xs with | [y, ..ys] => rewrite <- Option.someInjective found then List.foldMinByFirst f ys y

-- `List.maximum`, as for `List.minimum` above: the greatest of a list that
-- holds `most` and nothing else is `most`, an empty list has none, and what
-- it finds is in the list and at least each element. (`List.foldMaxGe`,
-- `List.leFoldMax` and `List.foldMaxMem` below are about folds of
-- `Nat.max`; these are about `Ord.max`, which `List.maximum` folds.)

--| Folding `Ord.max` from `most` over elements that are all `most`.
theorem List.foldMaxAll ∀ [auto ord: Ord a] (most: a) (xs: List a)
    (all: ∀ (x: a) => x ∈ xs → x = most):
    List.foldLeft xs most Ord.max = most :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite all x (Inl byComputing), Ord.maxSelf most then List.foldMaxAll most rest (y member => all y (Inr member))

theorem List.maximumAllEqual ∀ [auto ord: Ord a] (most: a) (xs: List a)
    (member: most ∈ xs)
    (all: ∀ (x: a) => x ∈ xs → x = most):
    List.maximum xs = Some most :=
  match xs with
    | [x, ..rest] =>
      rewrite all x (Inl byComputing) then Eq.cong Some (List.foldMaxAll most rest (y member => all y (Inr member)))

theorem List.maximumEmpty ∀ [auto ord: Ord a] (xs: List a) (none: ∀ (x: a) => x ∈ xs → Void): List.maximum xs = None :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => Void.impossible (none x (Inl byComputing))

--| Folding with `Ord.max` gives at least the start and each element, and
--| gives the start or an element.
theorem List.foldMaxGeStart ∀ [auto ord: Ord a] (xs: List a) (start: a): start <= List.foldLeft xs start Ord.max :=
  match xs with
    | [] => Ord.leRefl start
    | [y, ..ys] =>
      Ord.leTrans start
        (Ord.max start y)
        (List.foldLeft ys (Ord.max start y) Ord.max)
        (Ord.leMaxLeft start y)
        (List.foldMaxGeStart ys (Ord.max start y))

theorem List.foldMaxGeMember ∀ [auto ord: Ord a] (xs: List a) (start x: a)
    (h: x ∈ xs):
    x <= List.foldLeft xs start Ord.max :=
  match xs, h with
    | [], member => member.impossible
    | [y, ..ys], Inl same =>
      rewrite Eq.flipped same then
        Ord.leTrans y
          (Ord.max start y)
          (List.foldLeft ys (Ord.max start y) Ord.max)
          (Ord.leMaxRight start y)
          (List.foldMaxGeStart ys (Ord.max start y))
    | [y, ..ys], Inr member => List.foldMaxGeMember ys (Ord.max start y) x member

theorem List.foldMaxMember ∀ [auto ord: Ord a] (xs: List a) (start: a):
    (List.foldLeft xs start Ord.max = start) ∨ (List.foldLeft xs start Ord.max ∈ xs) :=
  match xs with
    | [] => Inl byComputing
    | [y, ..ys] =>
      match List.foldMaxMember ys (Ord.max start y) with
        | Inr member => Inr (Inr member)
        | Inl same =>
          match Ord.maxEither start y with
            | Inl isStart => Inl (Eq.trans same isStart)
            | Inr isY => Inr (Inl (Eq.trans same isY).flipped)

--| The greatest element is in the list and at least every element.
theorem List.maximumSome ∀ [auto ord: Ord a] (xs: List a) (most: a)
    (found: List.maximum xs = Some most):
    (most ∈ xs) ∧ (∀ (x: a) => x ∈ xs → x <= most) :=
  match xs with
    | [y, ..ys] =>
      let same := Option.someInjective found
      Both
        (match List.foldMaxMember ys y with
          | Inl isY => Inl (Eq.trans same.flipped isY).flipped
          | Inr member => Inr (rewrite same at member))
        (x member =>
          rewrite Eq.flipped same then
            match member with
              | Inl isY => rewrite Eq.flipped isY then List.foldMaxGeStart ys y
              | Inr inRest => List.foldMaxGeMember ys y x inRest)

--| A list with an element has a greatest one: it isn't `None`.
theorem List.maximumExists ∀ [auto ord: Ord a] (xs: List a) (x: a)
    (member: x ∈ xs):
    ∃ (most: a) => List.maximum xs = Some most :=
  match xs with | [y, ..ys] => Witness (List.foldLeft ys y Ord.max) byComputing

theorem List.maximumNone ∀ [auto ord: Ord a] (xs: List a)
    (none: List.maximum xs = None) (x: a)
    (member: x ∈ xs):
    Void :=
  match xs with | [y, ..ys] => Option.someNotNone (List.foldLeft ys y Ord.max) none

--| Lists with the same members have the same greatest member.
theorem List.maximumSameMembers ∀ [auto ord: Ord a] (xs ys: List a)
    (into: ∀ (v: a) => v ∈ xs → v ∈ ys)
    (back: ∀ (v: a) => v ∈ ys → v ∈ xs):
    List.maximum xs = List.maximum ys :=
  match mx: List.maximum xs with
    | None =>
      match my: List.maximum ys with
        | None => byComputing
        | Some y => Void.impossible (List.maximumNone xs mx y (back y (List.maximumSome ys y my).left))
    | Some x =>
      match my: List.maximum ys with
        | None => Void.impossible (List.maximumNone ys my x (into x (List.maximumSome xs x mx).left))
        | Some y =>
          let (Both xIn xMost) := List.maximumSome xs x mx
          let (Both yIn yMost) := List.maximumSome ys y my
          Eq.cong Some (Ord.leAntisymm x y (yMost x (into x xIn)) (xMost y (back y yIn)))

test "List.maximum and List.minimum" :=
  List.maximum [3, 9, 2] == Some 9 ∧ List.minimum [3, 9, 2] == Some 2 ∧ List.maximum ([]: List Nat) == None
