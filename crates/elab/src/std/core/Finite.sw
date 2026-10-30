-- core/Finite.sw. The `Finite` interface, the membership lemmas a derived
-- instance's proof is made of, and the instances for the core's finite types.
-- Loaded with the core: a data type declared in a program gets `Finite`
-- derived, and its proof writes `List.memAppendLeft`, `List.memAppendRight`
-- and `List.memConcatMap` in full (docs/proposals/decide.md §6.2, SW-807).

-- Membership in lists put together

-- An element of the first list is in the two joined.
theorem List.memAppendLeft (x: a): (xs: List a) → (ys: List a) → x ∈ xs → x ∈ List.append xs ys
  | Nil, ys, m => Void.exfalso m
  | Cons z zs, ys, Inl e => Inl e
  | Cons z zs, ys, Inr m => Inr (List.memAppendLeft x zs ys m)

-- And an element of the second.
theorem List.memAppendRight (x: a): (xs: List a) → (ys: List a) → x ∈ ys → x ∈ List.append xs ys
  | Nil, ys, m => m
  | Cons z zs, ys, m => Inr (List.memAppendRight x zs ys m)

-- What `f` makes from an element of `xs` is in `List.concatMap xs f`.
theorem List.memConcatMap (f: a → List b) (x: a) (y: b): (xs: List a) → x ∈ xs → y ∈ f x → y ∈ List.concatMap xs f
  | Nil, member, made => Void.exfalso member
  | Cons z zs, Inl same, made => List.memAppendLeft y (f z) (List.concatMap zs f) (J (w e => y ∈ f w) made (Eq.sym same))
  | Cons z zs, Inr later, made => List.memAppendRight y (f z) (List.concatMap zs f) (List.memConcatMap f x y zs later made)

-- Finite types

-- A type with a list of every value (docs/proposals/decide.md §6.2): `all`,
-- and `complete`, the proof that every value is on it. The list may repeat
-- a value; nothing here needs it not to (with `DecEq`, `List.distinctEq
-- Finite.all` is the list without repeats). A data type or record declared in
-- a program gets one derived when its constructors' fields all have one and
-- it isn't recursive (`T.%instFinite`): the constructors in the order they're
-- declared, each with every value of its fields, the first field varying
-- slowest, which is the order the derived `<` puts them in. A module's own
-- `instance` replaces it. `Finite.check` (std/Finite/Finite.sw) checks a
-- statement for every value by computing it.
interface Finite (a: Type) = {
  all: List a,
  complete: (x: a) → x ∈ all
}

instance Bool.instFinite: Finite Bool := {
  all = [False, True],
  complete = x => match x with
    | False => Inl rfl
    | True => Inr (Inl rfl)
}

instance Ordering.instFinite: Finite Ordering := {
  all = [Less, Equal, Greater],
  complete = x => match x with
    | Less => Inl rfl
    | Equal => Inr (Inl rfl)
    | Greater => Inr (Inr (Inl rfl))
}

-- Every option: `None`, then `Some` of every value.
def Option.allFinite [auto fin: Finite a]: List (Option a) := Cons None (List.concatMap Finite.all (x => [Some x]))

theorem Option.allFiniteComplete [auto fin: Finite a]: (o: Option a) → List.Mem o Option.allFinite
  | None => Inl rfl
  | Some x => Inr (List.memConcatMap (y => [Some y]) x (Some x) Finite.all (Finite.complete x) (Inl rfl))

instance Option.instFinite [auto fin: Finite a]: Finite (Option a) := { all = Option.allFinite, complete = Option.allFiniteComplete }

-- Every pair, the first value varying slowest.
def Pair.allFinite [auto finA: Finite a] [auto finB: Finite b]: List (Pair a b) :=
  List.concatMap Finite.all (x => List.concatMap Finite.all (y => [MkPair x y]))

theorem Pair.allFiniteComplete [auto finA: Finite a] [auto finB: Finite b]: (p: Pair a b) → List.Mem p Pair.allFinite
  | MkPair x y =>
    List.memConcatMap (u => List.concatMap Finite.all (v => [MkPair u v])) x (MkPair x y) Finite.all (Finite.complete x)
      (List.memConcatMap (v => [MkPair x v]) y (MkPair x y) Finite.all (Finite.complete y) (Inl rfl))

instance Pair.instFinite [auto finA: Finite a] [auto finB: Finite b]: Finite (Pair a b) := { all = Pair.allFinite, complete = Pair.allFiniteComplete }
