-- core/ListOptionPair.sw. List, `Pair` and `Option`: facts about their
-- constructors, small accessors, and decidable equality for each. Loaded with
-- the core: `List.instDecEq`, `Pair.instDecEq` and `Option.instDecEq` need
-- these, and `==` on those types needs the instances
-- (docs/proposals/prelude-slim.md §2.1).

-- Lists, continued

def List.IsNil: List a → Prop
  | Nil => Unit
  | Cons x xs => Void

theorem List.nilNotCons (x: a) (xs: List a): Not (Nil = Cons x xs)
  | p => J (y q => List.IsNil y) Trivial p

theorem List.consNotNil (x: a) (xs: List a): Not (Cons x xs = Nil)
  | p => List.nilNotCons x xs (Eq.sym p)

def List.headOr: List a → (fallback: a) → a
  | Nil, fallback => fallback
  | Cons x xs, fallback => x

def List.tailOf: List a → List a
  | Nil => Nil
  | Cons x xs => xs

@[noReceiver]
def List.decCons (x: a) (y: a) (xs: List a) (ys: List a):
    Decidable (x = y) → Decidable (xs = ys) → Decidable (Cons x xs = Cons y ys)
  | Yes p, Yes q => Yes (J (y' p' => Cons x xs = Cons y' ys) (Eq.cong (Cons x) q) p)
  | No r, dq => No (e => r (Eq.cong (.headOr x) e))
  | Yes p, No r => No (e => r (Eq.cong List.tailOf e))

-- Equality of lists, from equality of their elements.
@[noReceiver]
def List.decEq (d: (x: a) → (y: a) → Decidable (x = y)): (xs: List a) → (ys: List a) → Decidable (xs = ys)
  | Nil, Nil => Yes rfl
  | Nil, Cons y ys => No (List.nilNotCons y ys)
  | Cons x xs, Nil => No (List.consNotNil x xs)
  | Cons x xs, Cons y ys => List.decCons x y xs ys (d x y) (List.decEq d xs ys)

def Pair.decMk (x1: a) (x2: a) (y1: b) (y2: b):
    Decidable (x1 = x2) → Decidable (y1 = y2) → Decidable (MkPair x1 y1 = MkPair x2 y2)
  | Yes p, Yes q => Yes (J (x' p' => MkPair x1 y1 = MkPair x' y2) (Eq.cong (MkPair x1) q) p)
  | No r, dq => No (e => r (Eq.cong Pair.fst e))
  | Yes p, No r => No (e => r (Eq.cong Pair.snd e))

-- Equality of pairs, from equality of their parts.
@[noReceiver]
def Pair.decEq (da: (x: a) → (y: a) → Decidable (x = y)) (db: (x: b) → (y: b) → Decidable (x = y)):
    (p: Pair a b) → (q: Pair a b) → Decidable (p = q)
  | MkPair x1 y1, MkPair x2 y2 => Pair.decMk x1 x2 y1 y2 (da x1 x2) (db y1 y2)

def Option.IsNone: Option a → Prop
  | None => Unit
  | Some x => Void

theorem Option.noneNotSome (x: a): Not (None = Some x)
  | p => J (y q => Option.IsNone y) Trivial p

theorem Option.someNotNone (x: a): Not (Some x = None)
  | p => Option.noneNotSome x (Eq.sym p)

-- The value, or `fallback` if there isn't one.
def Option.getOrElse: Option a → (fallback: a) → a
  | None, fallback => fallback
  | Some x, fallback => x

def Option.decSome (x: a) (y: a): Decidable (x = y) → Decidable (Some x = Some y)
  | Yes p => Yes (Eq.cong Some p)
  | No r => No (e => r (Eq.cong (.getOrElse x) e))

-- Equality of optional values, from equality of the values.
@[noReceiver]
def Option.decEq (d: (x: a) → (y: a) → Decidable (x = y)): (m: Option a) → (n: Option a) → Decidable (m = n)
  | None, None => Yes rfl
  | None, Some y => No (Option.noneNotSome y)
  | Some x, None => No (Option.someNotNone x)
  | Some x, Some y => Option.decSome x y (d x y)

-- Every element, part or value satisfies the predicate: `List.All`,
-- `Option.All` and `Pair.All`, with `List.Any` and membership. They're in the
-- core because the induction principle generated for a nested type states its
-- hypotheses with them (`T.induct`, docs/syntax.md, "Nested data types"):
-- `Packets (items: List Packet)` gets `List.All motive items`.

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

-- `x` is an element of the list.
@[noReceiver]
def List.Mem (x: a) (xs: List a): Prop := List.Any (y => y = x) xs

-- The value, if there is one, satisfies `p`.
@[noReceiver]
def Option.All (p: a → Prop): Option a → Prop
  | None => Unit
  | Some x => p x

-- Both halves satisfy their predicates.
@[noReceiver]
def Pair.All (p: a → Prop) (q: b → Prop): Pair a b → Prop
  | MkPair x y => And (p x) (q y)

-- What holds of every element holds of each one.
theorem List.memOfAll (p: a → Prop): (xs: List a) → List.All p xs → (x: a) → List.Mem x xs → p x
  | Nil, all, x, member => Void.exfalso member
  | Cons y ys, Both here rest, x, Inl same => J (z e => p z) here same
  | Cons y ys, Both here rest, x, Inr member => List.memOfAll p ys rest x member

-- What holds of the value, if any, holds of the value there is.
theorem Option.memOfAll (p: a → Prop): (o: Option a) → Option.All p o → (x: a) → o = Some x → p x
  | None, all, x, e => Void.exfalso (Option.noneNotSome x e)
  | Some y, here, x, e => J (z s => p z) here (Eq.cong (.getOrElse y) e)
