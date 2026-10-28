-- Helpers for `Option`. These were in the core (docs/proposals/prelude-slim.md
-- stage 3); only the text readers needed them there.

def Option.flatMap: Option a → (f: a → Option b) → Option b
  | None, f => None
  | Some x, f => f x

def Option.map: Option a → (f: a → b) → Option b
  | None, f => None
  | Some x, f => Some (f x)

-- Two maps are one map of the composite.
theorem Option.mapMap (f: a → b) (g: b → c): (x: Option a) → Option.map (Option.map x f) g = Option.map x (y => g (f y))
  | None => rfl
  | Some y => rfl

-- `Some` is injective: equal `Some`s hold equal values.
theorem Option.someInjective (x: a) (y: a) (h: Some x = Some y): x = y := Eq.cong (.getOrElse x) h

-- Whether there is a value: `(Some 3).isSome` is `True`.
def Option.isSome: Option a → Bool
  | None => False
  | Some x => True

-- Whether there is none: `None.isNone` is `True`.
def Option.isNone: Option a → Bool
  | None => True
  | Some x => False

-- The first option if it is a `Some`, else the second: `x.orElse y`.
def Option.orElse: Option a → Option a → Option a
  | Some x, y => Some x
  | None, y => y

-- Combines two options of one type: a lone value stays, two values go through
-- `both`. `x.merge y (a b => a + b)` adds the values that are there, and is
-- `None` only when both are.
def Option.merge: Option a → Option a → (both: a → a → a) → Option a
  | Some x, Some y, both => Some (both x y)
  | Some x, None, both => Some x
  | None, Some y, both => Some y
  | None, None, both => None

-- `merge` for two types: `left` and `right` turn a lone value into the result,
-- `both` combines two. `x.alignWith y f g h` is `None` only when both are.
def Option.alignWith: Option a → Option b → (left: a → c) → (right: b → c) → (both: a → b → c) → Option c
  | Some x, Some y, left, right, both => Some (both x y)
  | Some x, None, left, right, both => Some (left x)
  | None, Some y, left, right, both => Some (right y)
  | None, None, left, right, both => None

-- `f` of the values when both are there, else `None`.
@[noReceiver]
def Option.map2 (f: a → b → c): Option a → Option b → Option c
  | Some x, Some y => Some (f x y)
  | _, _ => None

-- `f` of the values when all three are there, else `None`.
@[noReceiver]
def Option.map3 (f: a → b → c → d): Option a → Option b → Option c → Option d
  | Some x, Some y, Some z => Some (f x y z)
  | _, _, _ => None

-- `f` of the values when all four are there, else `None`.
@[noReceiver]
def Option.map4 (f: a → b → c → d → e): Option a → Option b → Option c → Option d → Option e
  | Some x, Some y, Some z, Some w => Some (f x y z w)
  | _, _, _, _ => None

theorem Option.map2None (f: a → b → c): (x: Option a) → Option.map2 f x None = None
  | None => rfl
  | Some x => rfl

theorem Option.map3None2 (f: a → b → c → d) (z: Option c): (x: Option a) → Option.map3 f x None z = None
  | None => rfl
  | Some x => rfl

theorem Option.map3None3 (f: a → b → c → d): (x: Option a) → (y: Option b) → Option.map3 f x y None = None
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

theorem Option.map4None2 (f: a → b → c → d → e) (z: Option c) (w: Option d): (x: Option a) → Option.map4 f x None z w = None
  | None => rfl
  | Some x => rfl

theorem Option.map4None3 (f: a → b → c → d → e) (w: Option d): (x: Option a) → (y: Option b) → Option.map4 f x y None w = None
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

theorem Option.map4None4 (f: a → b → c → d → e): (x: Option a) → (y: Option b) → (z: Option c) → Option.map4 f x y z None = None
  | None, y, z => rfl
  | Some x, None, z => rfl
  | Some x, Some y, None => rfl
  | Some x, Some y, Some z => rfl

-- `map2` is a `flatMap` then a `map`.
theorem Option.map2FlatMap (f: a → b → c) (y: Option b): (x: Option a) → Option.map2 f x y = Option.flatMap x (u => Option.map y (f u))
  | None => rfl
  | Some x =>
    match y with
      | None => rfl
      | Some v => rfl

-- A `map` after `map2`, `map3` or `map4` is one of the composite.
theorem Option.mapMap2 (f: a → b → c) (g: c → r): (x: Option a) → (y: Option b) →
    Option.map (Option.map2 f x y) g = Option.map2 (u v => g (f u v)) x y
  | None, y => rfl
  | Some x, None => rfl
  | Some x, Some y => rfl

theorem Option.mapMap3 (f: a → b → c → d) (g: d → r): (x: Option a) → (y: Option b) → (z: Option c) →
    Option.map (Option.map3 f x y z) g = Option.map3 (u v w => g (f u v w)) x y z
  | None, y, z => rfl
  | Some x, None, z => rfl
  | Some x, Some y, None => rfl
  | Some x, Some y, Some z => rfl

theorem Option.mapMap4 (f: a → b → c → d → e) (g: e → r): (x: Option a) → (y: Option b) → (z: Option c) → (w: Option d) →
    Option.map (Option.map4 f x y z w) g = Option.map4 (u v s t => g (f u v s t)) x y z w
  | None, y, z, w => rfl
  | Some x, None, z, w => rfl
  | Some x, Some y, None, w => rfl
  | Some x, Some y, Some z, None => rfl
  | Some x, Some y, Some z, Some w => rfl

-- With defaults for missing values, `map2` is `f` of the values or defaults,
-- when a default in either place makes `f` give the default result.
theorem Option.getOrElseMap2 (f: a → b → r) (da: a) (db: b) (d: r)
    (missing1: (y: b) → f da y = d)
    (missing2: (x: a) → f x db = d):
    (x: Option a) → (y: Option b) → Option.getOrElse (Option.map2 f x y) d = f (Option.getOrElse x da) (Option.getOrElse y db)
  | None, y => Eq.sym (missing1 _)
  | Some x, None => Eq.sym (missing2 _)
  | Some x, Some y => rfl

-- The same for three.
theorem Option.getOrElseMap3 (f: a → b → c → r) (da: a) (db: b) (dc: c) (d: r)
    (missing1: (y: b) → (z: c) → f da y z = d)
    (missing2: (x: a) → (z: c) → f x db z = d)
    (missing3: (x: a) → (y: b) → f x y dc = d):
    (x: Option a) → (y: Option b) → (z: Option c) →
    Option.getOrElse (Option.map3 f x y z) d = f (Option.getOrElse x da) (Option.getOrElse y db) (Option.getOrElse z dc)
  | None, y, z => Eq.sym (missing1 _ _)
  | Some x, None, z => Eq.sym (missing2 _ _)
  | Some x, Some y, None => Eq.sym (missing3 _ _)
  | Some x, Some y, Some z => rfl

-- The same for four.
theorem Option.getOrElseMap4 (f: a → b → c → e → r) (da: a) (db: b) (dc: c) (de: e) (d: r)
    (missing1: (y: b) → (z: c) → (w: e) → f da y z w = d)
    (missing2: (x: a) → (z: c) → (w: e) → f x db z w = d)
    (missing3: (x: a) → (y: b) → (w: e) → f x y dc w = d)
    (missing4: (x: a) → (y: b) → (z: c) → f x y z de = d):
    (x: Option a) → (y: Option b) → (z: Option c) → (w: Option e) →
    Option.getOrElse (Option.map4 f x y z w) d = f (Option.getOrElse x da) (Option.getOrElse y db) (Option.getOrElse z dc) (Option.getOrElse w de)
  | None, y, z, w => Eq.sym (missing1 _ _ _)
  | Some x, None, z, w => Eq.sym (missing2 _ _ _)
  | Some x, Some y, None, w => Eq.sym (missing3 _ _ _)
  | Some x, Some y, Some z, None => Eq.sym (missing4 _ _ _)
  | Some x, Some y, Some z, Some w => rfl

-- `Option.decEq` on two `Some`s gives the values' answer, wrapped by
-- `Option.decSome`, so `==` on them is `==` on the values.
theorem Option.decSomeToBool (x: a) (y: a): (d: Decidable (x = y)) → Decidable.toBool (Option.decSome x y d) = Decidable.toBool d
  | Yes p => rfl
  | No r => rfl

theorem Option.someBeqSome [auto eq: DecEq a] (x: a) (y: a): (Some x == Some y) = (x == y) :=
  Option.decSomeToBool x y (DecEq.decide x y)

theorem Option.someBeqSomeExample (x: Char): (Some x == Some 'A') = (x == 'A') := Option.someBeqSome x 'A'

-- Takes the option apart: `none` for `None`, else `some` of the value.
-- `x.fold 0 (v => v + 1)` is `0` for `None` and `v + 1` for `Some v`.
def Option.fold: Option a → (none: b) → (some: a → b) → b
  | None, none, some => none
  | Some x, none, some => some x

-- Whether there is a value and `p` holds for it (`None` is `False`).
def Option.any: Option a → (p: a → Bool) → Bool
  | None, p => False
  | Some x, p => p x

-- Whether `p` holds for the value, if any (`None` is `True`).
def Option.all: Option a → (p: a → Bool) → Bool
  | None, p => True
  | Some x, p => p x

-- Keeps the value only when `p` holds for it: `x |> .filter (v => v > 2)`.
def Option.filter: Option a → (p: a → Bool) → Option a
  | None, p => None
  | Some x, p => if p x then Some x else None

-- `orElse` is `Some v` when the first option is, or when the first is `None`
-- and the second is.
theorem Option.orElseEqSome (y: Option a) (v: a): (x: Option a) → Option.orElse x y = Some v → Or (x = Some v) (And (x = None) (y = Some v))
  | Some w, h => Inl h
  | None, h => Inr (Both rfl h)

theorem Option.orElseNone: (x: Option a) → Option.orElse x None = x
  | Some w => rfl
  | None => rfl

theorem Option.orElseSome (v: a) (y: Option a): Option.orElse (Some v) y = Some v := rfl

theorem Option.noneOrElse (y: Option a): Option.orElse None y = y := rfl

-- If `map f x` is `Some v`, then `x` held some `u` with `f u = v`.
theorem Option.mapEqSome [goal: Prop]: (x: Option a) → (f: a → b) → (v: b) → Option.map x f = Some v → ((u: a) → x = Some u → f u = v → goal) → goal
  | Some u, f, v, h, use => use u rfl (Option.someInjective (f u) v h)
  | None, f, v, h, use => Void.exfalso (Option.noneNotSome v h)

-- `map f x` is `None` exactly when `x` is.
theorem Option.mapEqNone: (x: Option a) → (f: a → b) → Option.map x f = None ↔ x = None
  | Some u, f => { forward = h => Void.exfalso (Option.someNotNone (f u) h), backward = h => Void.exfalso (Option.someNotNone u h) }
  | None, f => { forward = h => rfl, backward = h => rfl }

theorem Option.mapEqNoneExample (x: Option Nat) (h: Option.map x Succ = None): x = None := (Option.mapEqNone x Succ).forward h

-- If `flatMap f x` is `Some v`, then `x` held some `u` with `f u = Some v`.
theorem Option.flatMapEqSome [goal: Prop]: (x: Option a) → (f: a → Option b) → (v: b) → Option.flatMap x f = Some v → ((u: a) → x = Some u → f u = Some v → goal) → goal
  | Some u, f, v, h, use => use u rfl h
  | None, f, v, h, use => Void.exfalso (Option.noneNotSome v h)

-- If `filter p x` is `Some v`, then `x` is `Some v` and `p v` holds.
theorem Option.filterEqSome: (x: Option a) → (p: a → Bool) → (v: a) → Option.filter x p = Some v → And (x = Some v) (p v = True)
  | Some u, p, v, h =>
    match e: p u with
      | True => Both h (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective u v h))) e)
      | False => Void.exfalso (Option.noneNotSome v h)
  | None, p, v, h => Void.exfalso (Option.noneNotSome v h)

-- `orElse` of an option with itself is the option.
theorem Option.orElseSelf: (x: Option a) → Option.orElse x x = x
  | Some w => rfl
  | None => rfl

-- If `alignWith` is `Some v`, `v` came from one of the three arms: the left
-- value alone, the right alone, or both.
theorem Option.alignWithEqSome [goal: Prop] (left: a → c) (right: b → c) (both: a → b → c) (v: c):
    (x: Option a) → (y: Option b) → Option.alignWith x y left right both = Some v
      → ((u: a) → x = Some u → y = None → left u = v → goal)
      → ((w: b) → x = None → y = Some w → right w = v → goal)
      → ((u: a) → (w: b) → x = Some u → y = Some w → both u w = v → goal) → goal
  | Some u, Some w, h, onLeft, onRight, onBoth => onBoth u w rfl rfl (Option.someInjective (both u w) v h)
  | Some u, None, h, onLeft, onRight, onBoth => onLeft u rfl rfl (Option.someInjective (left u) v h)
  | None, Some w, h, onLeft, onRight, onBoth => onRight w rfl rfl (Option.someInjective (right w) v h)
  | None, None, h, onLeft, onRight, onBoth => Void.exfalso (Option.noneNotSome v h)

-- So a property each arm's result has, the result has.
theorem Option.alignWithHolds (q: c → Prop) (left: a → c) (right: b → c) (both: a → b → c)
    (onLeft: (u: a) → q (left u)) (onRight: (w: b) → q (right w)) (onBoth: (u: a) → (w: b) → q (both u w))
    (x: Option a) (y: Option b) (v: c) (h: Option.alignWith x y left right both = Some v): q v :=
  Option.alignWithEqSome [goal := q v] left right both v x y h
    (u ex ey e => rewrite <- e in onLeft u)
    (w ex ey e => rewrite <- e in onRight w)
    (u w ex ey e => rewrite <- e in onBoth u w)

-- `alignWith` is `None` exactly when both options are.
theorem Option.alignWithEqNone (left: a → c) (right: b → c) (both: a → b → c):
    (x: Option a) → (y: Option b) → Option.alignWith x y left right both = None ↔ And (x = None) (y = None)
  | Some u, Some w => { forward = h => Void.exfalso (Option.someNotNone (both u w) h), backward = h => Void.exfalso (Option.someNotNone u (And.left h)) }
  | Some u, None => { forward = h => Void.exfalso (Option.someNotNone (left u) h), backward = h => Void.exfalso (Option.someNotNone u (And.left h)) }
  | None, Some w => { forward = h => Void.exfalso (Option.someNotNone (right w) h), backward = h => Void.exfalso (Option.someNotNone w (And.right h)) }
  | None, None => { forward = h => Both rfl rfl, backward = h => rfl }

theorem Option.alignWithHoldsExample (x: Option Nat) (y: Option Nat) (v: Nat)
    (h: Option.alignWith x y Succ Succ (u w => Succ (u + w)) = Some v): Not (v = 0) :=
  Option.alignWithHolds (n => Not (n = 0)) Succ Succ (u w => Succ (u + w))
    (u => Nat.succNotZero u) (w => Nat.succNotZero w) (u w => Nat.succNotZero (u + w)) x y v h

-- `MkPair` is injective: equal pairs have equal parts.
theorem Pair.mkInjectiveFst (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): x1 = x2 := Eq.cong Pair.fst h
theorem Pair.mkInjectiveSnd (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): y1 = y2 := Eq.cong Pair.snd h

-- `==` on two pairs is `==` on both parts.
theorem Pair.mkBeqMk [auto eqA: DecEq a] [auto eqB: DecEq b] (x1: a) (y1: b) (x2: a) (y2: b): ((x1, y1) == (x2, y2)) = (x1 == x2 ∧ y1 == y2) :=
  match DecEq.decide x1 x2, DecEq.decide y1 y2 with
    | Yes p, Yes q => rfl
    | Yes p, No r => rfl
    | No r, dq => rfl

test "Option.isSome" := (Some 1).isSome == True ∧ (None: Option Nat).isSome == False
test "Option.isNone" := (Some 1).isNone == False ∧ (None: Option Nat).isNone == True
test "Option.orElse" := (Some 1).orElse (Some 2) == Some 1 ∧ (None: Option Nat).orElse (Some 2) == Some 2 ∧ (None: Option Nat).orElse None == None
test "Option.orElse chain" := ((None: Option Nat).orElse None |> .orElse (Some 3)) == Some 3
test "Option.merge" := (Some 1).merge (Some 2) (+) == Some 3
test "Option.merge lone" := (Some 1).merge None (+) == Some 1 ∧ (None: Option Nat).merge (Some 2) (+) == Some 2
test "Option.merge none" := (None: Option Nat).merge None (+) == None
test "Option.alignWith" := (Some 1).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 5
test "Option.alignWith lone" := (Some 1).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == Some 11 ∧ (None: Option Nat).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 25
test "Option.alignWith none" := (None: Option Nat).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == None
test "Option.fold" := (Some 4).fold 0 (+ 1) == 5 ∧ (None: Option Nat).fold 0 (+ 1) == 0
test "Option.any" := (Some 3).any (> 2) == True ∧ (Some 1).any (> 2) == False ∧ (None: Option Nat).any (> 2) == False
test "Option.all" := (Some 3).all (> 2) == True ∧ (Some 1).all (> 2) == False ∧ (None: Option Nat).all (> 2) == True
test "Option.filter" := (Some 3).filter (> 2) == Some 3 ∧ (Some 1).filter (> 2) == None ∧ (None: Option Nat).filter (> 2) == None
test "Option.filter in a pipe" := (Some 3 |> .filter (> 2)) == Some 3
