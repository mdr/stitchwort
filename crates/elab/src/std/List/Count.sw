--| Lemmas about counting: `List.count`, `List.occurrences`, filtering and
--| `countWith`, with the examples and tests that use them.

-- `List.count` is a fold with an accumulator; `List.occurrences` recurses on
-- the list, which suits proofs. They agree, so the lemmas below are stated
-- for `List.count` (the program's) and proved through `List.occurrences`.
-- Also here: counting and `List.scanLeft` over `++`, and permutations.

--| Rearranging sums, for the counting lemmas below.
theorem Nat.addRotate ∀ (a b c: Nat): (a + b) + c = b + (a + c) :=
  Eq.trans (Eq.cong (t => t + c) (Nat.addComm a b)) (Nat.addAssoc b a c)

theorem Nat.addLeftComm ∀ (a b c: Nat): a + (b + c) = b + (a + c) :=
  Eq.trans (Nat.addAssoc a b c).flipped (Nat.addRotate a b c)

theorem List.countStep ∀ (b: Bool) (k o: Nat): Nat.succIf k b + o = k + (Bool.toNat b + o) := match b with
  | True => (Nat.addSucc k o).flipped
  | False => byComputing

theorem List.countFold ∀ (xs: List a) (k: Nat) (p: a → Bool):
    List.foldLeft xs k (n x => Nat.succIf n (p x)) = k + List.occurrences xs p :=
  match xs with
    | [] => (Nat.addZero k).flipped
    | [x, ..xs] => Eq.trans (List.countFold xs (Nat.succIf k (p x)) p) (List.countStep (p x) k (List.occurrences xs p))

theorem List.countOccurrences ∀ (xs: List a) (p: a → Bool): List.count xs p = List.occurrences xs p :=
  List.countFold xs 0 p

theorem List.occurrencesSumBy ∀ (xs: List a) (p: a → Bool):
    List.occurrences xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] => rewrite List.sumByCons xs x (x => Bool.toNat (p x)), List.occurrencesSumBy xs p

--| A count is a sum of 1s and 0s, so the sum lemmas apply to it.
theorem List.countSumBy ∀ (xs: List a) (p: a → Bool): List.count xs p = List.sumBy xs (x => Bool.toNat (p x)) :=
  Eq.trans (List.countOccurrences xs p) (List.occurrencesSumBy xs p)

theorem List.occurrencesAppend ∀ (xs ys: List a) (p: a → Bool):
    List.occurrences (List.append xs ys) p = List.occurrences xs p + List.occurrences ys p :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      Eq.trans
        (Eq.cong (t => Bool.toNat (p x) + t) (List.occurrencesAppend xs ys p))
        (Eq.flipped (Nat.addAssoc (Bool.toNat (p x)) (List.occurrences xs p) (List.occurrences ys p)))

theorem List.countNil ∀ (p: a → Bool): List.count [] p = 0 := byComputing

theorem List.countCons ∀ (xs: List a) (x: a) (p: a → Bool):
    List.count [x, ..xs] p = Bool.toNat (p x) + List.count xs p :=
  Eq.trans
    (List.countOccurrences [x, ..xs] p)
    (Eq.cong (n => Bool.toNat (p x) + n) (List.countOccurrences xs p).flipped)

theorem List.countAppend ∀ (xs ys: List a) (p: a → Bool):
    List.count (List.append xs ys) p = List.count xs p + List.count ys p :=
  calc (xs ++ ys).count p
    _ = (xs ++ ys).occurrences p := List.countOccurrences (List.append xs ys) p
    _ = xs.occurrences p + ys.occurrences p := List.occurrencesAppend xs ys p
    _ = xs.count p + ys.occurrences p := Eq.cong (n => n + List.occurrences ys p) (List.countOccurrences xs p).flipped
    _ = xs.count p + ys.count p := Eq.cong (n => List.count xs p + n) (List.countOccurrences ys p).flipped

--| The length of a `filter` is the `count` with the same test.
theorem List.lengthFilter ∀ (xs: List a) (p: a → Bool): List.length (List.filter xs p) = List.count xs p :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x p, <- List.lengthFilter rest p then
        match keep: p x with
          | True | False => byComputing

--| A count is at most the length, and so is a `filter`'s length; filtering
--| out an element that is there makes the list shorter.
theorem List.countLeLength ∀ (xs: List a) (p: a → Bool): List.count xs p ≤ List.length xs := match xs with
  | [] => Nat.leRefl 0
  | [x, ..rest] => rewrite List.countCons rest x p then arithmetic [List.countLeLength rest p, Bool.toNatLeOne (p x)]

theorem List.lengthFilterLe ∀ (xs: List a) (p: a → Bool): List.length (List.filter xs p) ≤ List.length xs :=
  rewrite List.lengthFilter xs p then List.countLeLength xs p

theorem List.lengthFilterLt ∀ (p: a → Bool) (x: a)
    (dropped: p x = False) (xs: List a)
    (member: x ∈ xs):
    List.length (List.filter xs p) < List.length xs :=
  match xs, member with
    | [], member => member.impossible
    | [y, ..rest], Inl same => rewrite same, dropped then arithmetic [List.lengthFilterLe rest p]
    | [y, ..rest], Inr later =>
      match p y with
        | True => List.lengthFilterLt p x dropped rest later
        | False => arithmetic [List.lengthFilterLt p x dropped rest later]

--| An element that passes makes the count positive, and the other way
--| round, for an element counted by `== c`.
theorem List.countPositive ∀ (xs: List a) (p: a → Bool) (x: a)
    (member: x ∈ xs)
    (passes: p x = True):
    0 < List.count xs p :=
  match xs, member with
    | [], member => member.impossible
    | [y, ..rest], Inl same => rewrite List.countCons rest y p, same, passes then arithmetic
    | [y, ..rest], Inr later =>
      rewrite List.countCons rest y p then arithmetic [List.countPositive rest p x later passes]

theorem List.memOfCountPositive ∀ [auto eq: DecEq a] (c: a) (xs: List a) (positive: 0 < List.count xs (== c)): c ∈ xs :=
  match xs with
    | [x, ..rest] =>
      match t: x == c with
        | True => Inl t.read
        | False => Inr (List.memOfCountPositive c rest (arithmetic [List.countCons rest x (== c)]))

--| Filtering twice is filtering once by both tests.
theorem List.filterFilter ∀ (p q: a → Bool) (xs: List a):
    List.filter (List.filter xs p) q = List.filter xs (x => p x ∧ q x) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] => rewrite <- List.filterFilter p q rest then cases

theorem List.countFalse ∀ (xs: List a): List.count xs (x => False) = 0 := match xs with
  | [] => byComputing
  | [x, ..rest] => List.countFalse rest

--| A count where no element passes is 0.
theorem List.countNone ∀ (xs: List a) (p: a → Bool) (none: ∀ (x: a) => x ∈ xs → p x = False): List.count xs p = 0 :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countCons rest x p, none x (Inl byComputing), List.countNone rest p (y member => none y (Inr member))

theorem List.anyEmpty ∀ (xs: List a) (p: a → Bool) (empty: List.length xs = 0): List.any xs p = False := match xs with
  | [] => byComputing
  | [x, ..rest] => Void.impossible (Nat.succNotZero (List.length rest) empty)

--| The length of a `flatMap` is the sum of the lengths of the lists it joins.
theorem List.lengthFlatMap ∀ (f: a → List b) (xs: List a):
    List.length (List.flatMap xs f) = List.sumBy xs (x => List.length (f x)) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.sumByCons rest x (x => List.length (f x)), <- List.lengthFlatMap f rest then
        List.lengthAppend (f x) (List.flatMap rest f)

theorem List.lengthFlatMapExample: List.length (List.flatMap [1, 2, 3] (n => List.replicate n n)) = 6 := byComputing

--| Counting over a `flatMap` adds up the counts over each list it joins.
theorem List.countFlatMap ∀ (f: a → List b) (p: b → Bool) (xs: List a):
    List.count (List.flatMap xs f) p = List.sumBy xs (x => List.count (f x) p) :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      rewrite List.countAppend (f x) (List.flatMap rest f) p,
          List.sumByCons rest x (x => List.count (f x) p),
          List.countFlatMap f p rest

--| `answer` of `items` have the property `p`: counting by a proposition,
--| for a `p` with no decision procedure to count with (a statement that
--| quantifies over functions, say). With a procedure, [`List.countWithIff`]
--| says the answer is [`List.count`]. For counting the values `x` with `p x`
--| over all values, see [`List.NumberWith`].
@[noReceiver]
def List.CountWith (p: a → Prop): (items: List a) → (answer: Nat) → Prop
  | [], answer => answer = 0
  | [item, ..rest], answer =>
    (p item ∧ ∃ (others: Nat) => List.CountWith p rest others ∧ answer = others + 1)
      ∨ (¬p item ∧ List.CountWith p rest answer)

--| Counting by a proposition is [`List.count`] by a `Bool` that decides it.
theorem List.countWithIff ∀ [p: a → Prop] (decide: a → Bool)
    (decides: ∀ (item: a) => decide item = True ↔ p item)
    (items: List a) (answer: Nat):
    List.CountWith p items answer ↔ answer = items.count decide :=
  match items with
    | [] => { forward = none => none, backward = none => none }
    | [item, ..rest] =>
      let later := List.countWithIff decide decides rest
      rewrite List.countCons rest item decide then
        match decided: decide item with
          | True =>
            let holds := (decides item).forward decided
            {
              forward = counted =>
                match counted with
                  | Inl (Both yes (Witness others (Both number more))) => arithmetic [(later others).forward number]
                  | Inr (Both no number) => (no holds).impossible,
              backward = same =>
                Inl
                  (Both holds
                    (Witness
                      (rest.count decide)
                      (Both ((later (rest.count decide)).backward byComputing) (arithmetic))))
            }
          | False =>
            let fails: ¬p item := holds => Bool.falseNotTrue (Eq.trans decided.flipped ((decides item).backward holds))
            {
              forward = counted =>
                match counted with
                  | Inl (Both yes more) => (fails yes).impossible
                  | Inr (Both no number) => (later answer).forward number,
              backward = same => Inr (Both fails ((later answer).backward (arithmetic)))
            }
