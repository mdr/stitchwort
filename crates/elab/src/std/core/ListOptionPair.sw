--| List, `Pair` and `Option`: facts about their
--| constructors, small accessors, and decidable equality for each.
-- Loaded with the core: `List.instDecEq`, `Pair.instDecEq` and
-- `Option.instDecEq` need these, and `==` on those types needs the instances
-- (docs/proposals/prelude-slim.md §2.1).

-- Lists, continued

--| `Unit` (true) for the empty list and `Void` (false) for any other: how `Nil ≠ Cons x xs` is proved.
def List.IsNil: (xs: List a) → Prop
  | [] => Unit
  | [x, ..xs] => Void

theorem List.nilNotCons ∀ (x: a) (xs: List a): [] ≠ [x, ..xs]
  | p => J (y q => List.IsNil y) Trivial p

theorem List.consNotNil ∀ (x: a) (xs: List a): [x, ..xs] ≠ []
  | p => List.nilNotCons x xs (Eq.sym p)

--| The first element, or `fallback` for an empty list. A result equal to
--| `fallback` doesn't say the list was empty; `List.head` does. O(1).
def List.headOr: (xs: List a) → (fallback: a) → a
  | [], fallback => fallback
  | [x, ..xs], fallback => x

--| The list without its first element, `[]` for an empty list; the same as
--| `List.drop xs 1`, in O(1).
def List.tailOf: (xs: List a) → List a
  | [] => []
  | [x, ..xs] => xs

--| Decides whether two non-empty lists are equal, from decisions about their heads and tails.
@[noReceiver]
def List.decCons (x y: a) (xs ys: List a)
    (headEq: Decidable (x = y))
    (tailEq: Decidable (xs = ys)):
    Decidable ([x, ..xs] = [y, ..ys]) :=
  Decidable.map
    (Decidable.and headEq tailEq)
    (pq => J (y' p' => [x, ..xs] = [y', ..ys]) (Eq.cong (Cons x) (And.right pq)) (And.left pq))
    (e => Both (Eq.cong (.headOr x) e) (Eq.cong List.tailOf e))

--| Equality of lists, from equality of their elements.
@[noReceiver]
def List.decEq (d: (x: a) → (y: a) → Decidable (x = y)): (xs: List a) → (ys: List a) → Decidable (xs = ys)
  | [], [] => Decidable.yes rfl
  | [], [y, ..ys] => Decidable.no (List.nilNotCons y ys)
  | [x, ..xs], [] => Decidable.no (List.consNotNil x xs)
  | [x, ..xs], [y, ..ys] => List.decCons x y xs ys (d x y) (List.decEq d xs ys)

--| Decides whether two pairs are equal, from decisions about their parts.
def Pair.decMk (x1 x2: a) (y1 y2: b)
    (fstEq: Decidable (x1 = x2))
    (sndEq: Decidable (y1 = y2)):
    Decidable (MkPair x1 y1 = MkPair x2 y2) :=
  Decidable.map
    (Decidable.and fstEq sndEq)
    (pq => J (x' p' => MkPair x1 y1 = MkPair x' y2) (Eq.cong (MkPair x1) (And.right pq)) (And.left pq))
    (e => Both (Eq.cong Pair.fst e) (Eq.cong Pair.snd e))

--| Equality of pairs, from equality of their parts.
@[noReceiver]
def Pair.decEq (da: (x: a) → (y: a) → Decidable (x = y)) (db: (x: b) → (y: b) → Decidable (x = y)):
    (p: Pair a b) → (q: Pair a b) → Decidable (p = q)
  | MkPair x1 y1, MkPair x2 y2 => Pair.decMk x1 x2 y1 y2 (da x1 x2) (db y1 y2)

--| `Unit` (true) for `None` and `Void` (false) for a `Some`: how `None ≠ Some x` is proved.
def Option.IsNone: (option: Option a) → Prop
  | None => Unit
  | Some x => Void

theorem Option.noneNotSome ∀ (x: a): None ≠ Some x
  | p => J (y q => Option.IsNone y) Trivial p

theorem Option.someNotNone ∀ (x: a): Some x ≠ None
  | p => Option.noneNotSome x (Eq.sym p)

--| The value, or `fallback` if there isn't one.
def Option.getOrElse: (option: Option a) → (fallback: a) → a
  | None, fallback => fallback
  | Some x, fallback => x

--| Decides whether two `Some`s are equal, from a decision about their values.
def Option.decSome (x y: a) (dec: Decidable (x = y)): Decidable (Some x = Some y) :=
  Decidable.map dec (Eq.cong Some) (Eq.cong (.getOrElse x))

--| Equality of optional values, from equality of the values.
@[noReceiver]
def Option.decEq (d: (x: a) → (y: a) → Decidable (x = y)): (m: Option a) → (n: Option a) → Decidable (m = n)
  | None, None => Decidable.yes rfl
  | None, Some y => Decidable.no (Option.noneNotSome y)
  | Some x, None => Decidable.no (Option.someNotNone x)
  | Some x, Some y => Option.decSome x y (d x y)

-- Every element, part or value satisfies the predicate: `List.All`,
-- `Option.All` and `Pair.All`, with `List.Any` and membership. They're in the
-- core because the induction principle generated for a nested type states its
-- hypotheses with them (`T.induct`, docs/syntax.md, "Nested data types"):
-- `Packets (items: List Packet)` gets `List.All motive items`.

--| Every element of the list satisfies `p`.
@[noReceiver]
def List.All (p: a → Prop): (xs: List a) → Prop
  | [] => Unit
  | [x, ..xs] => (p x) ∧ (List.All p xs)

--| Some element of the list satisfies `p`.
@[noReceiver]
def List.Any (p: a → Prop): (xs: List a) → Prop
  | [] => Void
  | [x, ..xs] => (p x) ∨ (List.Any p xs)

--| `x` is an element of the list.
@[noReceiver]
def List.Mem (x: a) (xs: List a): Prop := List.Any (y => y = x) xs

--| The value, if there is one, satisfies `p`.
@[noReceiver]
def Option.All (p: a → Prop): (option: Option a) → Prop
  | None => Unit
  | Some x => p x

--| Both halves satisfy their predicates.
@[noReceiver]
def Pair.All (p: a → Prop) (q: b → Prop): (pair: Pair a b) → Prop
  | MkPair x y => (p x) ∧ (q y)

--| What holds of every element holds of each one.
theorem List.memOfAll ∀ (p: a → Prop): ∀ (xs: List a) => List.All p xs → ∀ (x: a) => List.Mem x xs → p x
  | [], all, x, member => Void.exfalso member
  | [y, ..ys], Both here rest, x, Inl same => J (z e => p z) here same
  | [y, ..ys], Both here rest, x, Inr member => List.memOfAll p ys rest x member

--| What holds of the value, if any, holds of the value there is.
theorem Option.memOfAll ∀ (p: a → Prop): ∀ (o: Option a) => Option.All p o → ∀ (x: a) => o = Some x → p x
  | None, all, x, e => Void.exfalso (Option.noneNotSome x e)
  | Some y, here, x, e => J (z s => p z) here (Eq.cong (.getOrElse y) e)
