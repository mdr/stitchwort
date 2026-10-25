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
