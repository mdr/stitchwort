--| Helpers for `Option`: `map`, `flatMap`, `orElse`, `merge`, `map2` and the
--| like. Their lemmas are in Option/Lemmas.sw, except `Option.mapCong`.

--| `f` of the value, which may itself be missing, or `None` if there is no value:
--| `(Some 4).flatMap (n => if n > 2 then Some (n * 2) else None)` is `Some 8`.
def Option.flatMap: (option: Option a) → (f: a → Option b) → Option b
  | None, f => None
  | Some x, f => f x

--| `f` of the value, if there is one: `(Some 3).map (n => n + 1)` is `Some 4`, and `None` stays `None`
--| ([`Option.mapEqNone`]).
def Option.map: (option: Option a) → (f: a → b) → Option b
  | None, f => None
  | Some x, f => Some (f x)

--| Mapping with functions that agree everywhere gives the same result.
-- Here, beside `Option.map`, not in Option/Lemmas.sw: `rewrite` and
-- `decreasing` look it up by name wherever `Option.map` is loaded
-- (crates/elab/src/congruence.rs). Its shape is `List.mapCong`'s.
theorem Option.mapCong ∀ (x: Option a) (f1 f2: a → b)
    (ef: ∀ (y: a) => f1 y = f2 y):
    Option.map x f1 = Option.map x f2 :=
  match x with
    | None => rfl
    | Some y => Eq.cong Some (ef y)

--| Whether there is a value: `(Some 3).isSome` is `True`.
def Option.isSome: (option: Option a) → Bool
  | None => False
  | Some x => True

--| `o.isSome` reads as "`o` is a `Some`", and `= False` as `o = None`.
@[reading]
theorem Option.isSomeReads ∀ (o: Option a): Option.isSome o ↔ ∃ (x: a) => o = Some x := match o with
  | None => {
    forward = h => Void.exfalso (Bool.falseNotTrue h),
    backward = h => Exists.elim h (x found => Void.exfalso (Option.noneNotSome x found))
  }
  | Some y => { forward = h => Witness y rfl, backward = h => rfl }

@[reading]
theorem Option.isSomeReadsFalse ∀ (o: Option a): Option.isSome o = False ↔ o = None := match o with
  | None => { forward = h => rfl, backward = h => rfl }
  | Some y => {
    forward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h)),
    backward = h => Void.exfalso (Option.noneNotSome y (Eq.sym h))
  }

--| Whether there is none: `None.isNone` is `True`.
def Option.isNone: (option: Option a) → Bool
  | None => True
  | Some x => False

--| `o.isNone` reads as `o = None`, and `= False` as "`o` is a `Some`".
@[reading]
theorem Option.isNoneReads ∀ (o: Option a): Option.isNone o ↔ o = None := match o with
  | None => { forward = h => rfl, backward = h => rfl }
  | Some y => {
    forward = h => Void.exfalso (Bool.falseNotTrue h),
    backward = h => Void.exfalso (Option.noneNotSome y (Eq.sym h))
  }

@[reading]
theorem Option.isNoneReadsFalse ∀ (o: Option a): Option.isNone o = False ↔ ∃ (x: a) => o = Some x := match o with
  | None => {
    forward = h => Void.exfalso (Bool.falseNotTrue (Eq.sym h)),
    backward = h => Exists.elim h (x found => Void.exfalso (Option.noneNotSome x found))
  }
  | Some y => { forward = h => Witness y rfl, backward = h => rfl }

--| The first option if it is a `Some`, else the second: `x.orElse y` ([`Option.orElseEqSome`]).
def Option.orElse: (option: Option a) → (other: Option a) → Option a
  | Some x, y => Some x
  | None, y => y

--| Combines two options of one type: a lone value stays, two values go through
--| `both`. `x.merge y (a b => a + b)` adds the values that are there, and is
--| `None` only when both are.
def Option.merge: (option: Option a) → (other: Option a) → (both: a → a → a) → Option a
  | Some x, Some y, both => Some (both x y)
  | Some x, None, both => Some x
  | None, Some y, both => Some y
  | None, None, both => None

--| `merge` for two types: `left` and `right` turn a lone value into the result,
--| `both` combines two. `x.alignWith y f g h` is `None` only when both are.
def Option.alignWith: (option: Option a)
      → (other: Option b)
      → (left: a → c)
      → (right: b → c)
      → (both: a → b → c)
      → Option c
  | Some x, Some y, left, right, both => Some (both x y)
  | Some x, None, left, right, both => Some (left x)
  | None, Some y, left, right, both => Some (right y)
  | None, None, left, right, both => None

--| `f` of the values when both are there, else `None`.
@[noReceiver]
def Option.map2 (f: a → b → c): (first: Option a) → (second: Option b) → Option c
  | Some x, Some y => Some (f x y)
  | _, _ => None

--| `f` of the values when all three are there, else `None`.
@[noReceiver]
def Option.map3 (f: a → b → c → d): (first: Option a) → (second: Option b) → (third: Option c) → Option d
  | Some x, Some y, Some z => Some (f x y z)
  | _, _, _ => None

--| `f` of the values when all four are there, else `None`.
@[noReceiver]
def Option.map4 (f: a → b → c → d → e):
    (first: Option a) → (second: Option b) → (third: Option c) → (fourth: Option d) → Option e
  | Some x, Some y, Some z, Some w => Some (f x y z w)
  | _, _, _, _ => None

--| Takes the option apart: `none` for `None`, else `some` of the value.
--| `x.fold 0 (v => v + 1)` is `0` for `None` and `v + 1` for `Some v`.
--| `none` is an argument, so one that performs runs whatever `x` is:
--| `x.fold (Fail.fail message) (v => v)` always fails, where
--| `Fail.need x message` fails only for `None`.
def Option.fold: (option: Option a) → (none: b) → (some: a → b) → b
  | None, none, some => none
  | Some x, none, some => some x

--| Whether there is a value and `p` holds for it (`None` is `False`).
def Option.any: (option: Option a) → (p: a → Bool) → Bool
  | None, p => False
  | Some x, p => p x

--| Whether `p` holds for the value, if any (`None` is `True`).
def Option.all: (option: Option a) → (p: a → Bool) → Bool
  | None, p => True
  | Some x, p => p x

--| Keeps the value only when `p` holds for it: `x |> .filter (v => v > 2)`.
def Option.filter: (option: Option a) → (p: a → Bool) → Option a
  | None, p => None
  | Some x, p => if p x then Some x else None

--| The value as a one-element list, or the empty list.
def Option.toList: (option: Option a) → List a
  | None => []
  | Some x => [x]

--| Removes one layer of option: `Some (Some 3)` becomes `Some 3`, and a `None` at either layer
--| becomes `None`. It is `flatMap id`: `(Some (Some 3)).flatten` is `Some 3`.
def Option.flatten: (nested: Option (Option a)) → Option a
  | None => None
  | Some inner => inner

theorem Option.flattenFlatMap ∀ (x: Option (Option a)): Option.flatten x = Option.flatMap x id := match x with
  | None => rfl
  | Some inner => rfl

theorem Option.toListExample: (Some 3).toList = [3] := rfl

test "Option.flatten" :=
  (Some (Some 3)).flatten == Some 3
    ∧ (Some (None: Option Nat)).flatten == None
    ∧ (None: Option (Option Nat)).flatten == None
test "Option.isSome" := (Some 1).isSome == True ∧ (None: Option Nat).isSome == False
test "Option.isNone" := (Some 1).isNone == False ∧ (None: Option Nat).isNone == True
test "Option.orElse" :=
  (Some 1).orElse (Some 2) == Some 1
    ∧ (None: Option Nat).orElse (Some 2) == Some 2
    ∧ (None: Option Nat).orElse None == None
test "Option.orElse chain" := ((None: Option Nat).orElse None |> .orElse (Some 3)) == Some 3
test "Option.merge" := (Some 1).merge (Some 2) (+) == Some 3
test "Option.merge lone" := (Some 1).merge None (+) == Some 1 ∧ (None: Option Nat).merge (Some 2) (+) == Some 2
test "Option.merge none" := (None: Option Nat).merge None (+) == None
test "Option.alignWith" := (Some 1).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 5
test "Option.alignWith lone" :=
  (Some 1).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == Some 11
    ∧ (None: Option Nat).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 25
test "Option.alignWith none" := (None: Option Nat).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == None
test "Option.fold" := (Some 4).fold 0 (+ 1) == 5 ∧ (None: Option Nat).fold 0 (+ 1) == 0
test "Option.any" := (Some 3).any (> 2) == True ∧ (Some 1).any (> 2) == False ∧ (None: Option Nat).any (> 2) == False
test "Option.all" := (Some 3).all (> 2) == True ∧ (Some 1).all (> 2) == False ∧ (None: Option Nat).all (> 2) == True
test "Option.filter" :=
  (Some 3).filter (> 2) == Some 3 ∧ (Some 1).filter (> 2) == None ∧ (None: Option Nat).filter (> 2) == None
test "Option.filter in a pipe" := (Some 3 |> .filter (> 2)) == Some 3
