--| The `Finite` interface, the membership lemmas a derived
--| instance's proof is made of, and the instances for the core's finite types.
-- Loaded with the core: a data type declared in a program gets `Finite`
-- derived, and its proof writes `List.memAppendLeft`, `List.memAppendRight`
-- and `List.memConcatMap` in full (docs/proposals/decide.md §6.2, SW-807).

-- Membership in lists put together

--| An element of the first list is in the two joined.
theorem List.memAppendLeft ∀ (x: a) (xs ys: List a) (h: x ∈ xs): x ∈ List.append xs ys := match xs, h with
  | [], m => Void.exfalso m
  | [z, ..zs], Inl e => Inl e
  | [z, ..zs], Inr m => Inr (List.memAppendLeft x zs ys m)

--| An element of the second list is in the two joined.
theorem List.memAppendRight ∀ (x: a) (xs ys: List a) (m: x ∈ ys): x ∈ List.append xs ys := match xs with
  | [] => m
  | [z, ..zs] => Inr (List.memAppendRight x zs ys m)

--| What `f` makes from an element of `xs` is in `List.concatMap xs f`.
theorem List.memConcatMap ∀ (f: a → List b) (x: a) (y: b) (xs: List a)
    (member: x ∈ xs)
    (made: y ∈ f x):
    y ∈ List.concatMap xs f :=
  match xs, member with
    | [], member => Void.exfalso member
    | [z, ..zs], Inl same => List.memAppendLeft y (f z) (List.concatMap zs f) (J (w e => y ∈ f w) made (Eq.sym same))
    | [z, ..zs], Inr later => List.memAppendRight y (f z) (List.concatMap zs f) (List.memConcatMap f x y zs later made)

-- Finite types

--| A type with a list of every value: `all`, and `complete`, the proof that
--| every value is on it. The list may repeat a value; nothing here needs it not
--| to (with `DecEq`, `List.uniqueDecEq Finite.all` is the list without repeats).
--| A data type or record declared in a program gets one derived when its
--| constructors' fields all have one and it isn't recursive (`T.%instFinite`):
--| the constructors in the order they're declared, each with every value of its
--| fields, the first field varying slowest, which is the order the derived `<`
--| puts them in. A module's own `instance` replaces it. `Finite.check`
--| (std/Finite/Finite.sw) checks a statement for every value by computing it.
-- (docs/proposals/decide.md §6.2)
interface Finite (a: Type) = { all: List a, complete: ∀ (x: a) => x ∈ all }

instance Bool.instFinite: Finite Bool := {
  all = [False, True],
  complete = x =>
    match x with
      | False => Inl rfl
      | True => Inr (Inl rfl)
}

instance Ordering.instFinite: Finite Ordering := {
  all = [Less, Equal, Greater],
  complete = x =>
    match x with
      | Less => Inl rfl
      | Equal => Inr (Inl rfl)
      | Greater => Inr (Inr (Inl rfl))
}

--| Every option: `None`, then `Some` of every value.
def Option.allFinite [auto fin: Finite a]: List (Option a) := [None, ..List.concatMap Finite.all (x => [Some x])]

theorem Option.allFiniteComplete ∀ [auto fin: Finite a] (o: Option a): List.Mem o Option.allFinite := match o with
  | None => Inl rfl
  | Some x => Inr (List.memConcatMap (y => [Some y]) x (Some x) Finite.all (Finite.complete x) (Inl rfl))

instance Option.instFinite [auto fin: Finite a]: Finite (Option a) :=
  { all = Option.allFinite, complete = Option.allFiniteComplete }

--| Every pair, the first value varying slowest.
def Pair.allFinite [auto finA: Finite a] [auto finB: Finite b]: List (Pair a b) :=
  List.concatMap Finite.all (x => List.concatMap Finite.all (y => [MkPair x y]))

theorem Pair.allFiniteComplete ∀ [auto finA: Finite a] [auto finB: Finite b] (p: Pair a b): List.Mem p Pair.allFinite :=
  match p with
    | MkPair x y =>
      List.memConcatMap
        (u => List.concatMap Finite.all (v => [MkPair u v]))
        x
        (MkPair x y)
        Finite.all
        (Finite.complete x)
        (List.memConcatMap (v => [MkPair x v]) y (MkPair x y) Finite.all (Finite.complete y) (Inl rfl))

instance Pair.instFinite [auto finA: Finite a] [auto finB: Finite b]: Finite (Pair a b) :=
  { all = Pair.allFinite, complete = Pair.allFiniteComplete }
