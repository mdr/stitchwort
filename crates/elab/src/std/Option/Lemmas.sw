--| Lemmas about the `Option` helpers (Option/Option.sw), and about `==` on
--| options and pairs.

--| Two maps are one map of the composite.
theorem Option.mapMap ∀ (f: a → b) (g: b → c) (x: Option a):
    Option.map (Option.map x f) g = Option.map x (y => g (f y)) :=
  match x with
    | None => byComputing
    | Some y => byComputing

--| Mapping with the identity changes nothing.
theorem Option.mapId ∀ (x: Option a): Option.map x (y => y) = x := match x with
  | None => byComputing
  | Some y => byComputing

--| `Some` is injective: equal `Some`s hold equal values.
theorem Option.someInjective ∀ [x y: a] (h: Some x = Some y): x = y := Eq.cong (.getOrElse x) h

--| `map2` with `None` second is `None`.
theorem Option.map2None ∀ (f: a → b → c) (x: Option a): Option.map2 f x None = None := match x with
  | None => byComputing
  | Some x => byComputing

theorem Option.map3None2 ∀ (f: a → b → c → d) (z: Option c) (x: Option a): Option.map3 f x None z = None := match x with
  | None => byComputing
  | Some x => byComputing

theorem Option.map3None3 ∀ (f: a → b → c → d) (x: Option a) (y: Option b): Option.map3 f x y None = None :=
  match x, y with
    | None, y => byComputing
    | Some x, None => byComputing
    | Some x, Some y => byComputing

theorem Option.map4None2 ∀ (f: a → b → c → d → e) (z: Option c) (w: Option d) (x: Option a):
    Option.map4 f x None z w = None :=
  match x with
    | None => byComputing
    | Some x => byComputing

theorem Option.map4None3 ∀ (f: a → b → c → d → e) (w: Option d) (x: Option a) (y: Option b):
    Option.map4 f x y None w = None :=
  match x, y with
    | None, y => byComputing
    | Some x, None => byComputing
    | Some x, Some y => byComputing

theorem Option.map4None4 ∀ (f: a → b → c → d → e) (x: Option a) (y: Option b) (z: Option c):
    Option.map4 f x y z None = None :=
  match x, y, z with
    | None, y, z => byComputing
    | Some x, None, z => byComputing
    | Some x, Some y, None => byComputing
    | Some x, Some y, Some z => byComputing

--| `map2` is a `flatMap` then a `map`.
theorem Option.map2FlatMap ∀ (f: a → b → c) (y: Option b) (x: Option a):
    Option.map2 f x y = Option.flatMap x (u => Option.map y (f u)) :=
  match x with
    | None => byComputing
    | Some x =>
      match y with
        | None => byComputing
        | Some v => byComputing

--| A `map` after `map2`, `map3` or `map4` is one of the composite.
theorem Option.mapMap2 ∀ (f: a → b → c) (g: c → r) (x: Option a) (y: Option b):
    Option.map (Option.map2 f x y) g = Option.map2 (u v => g (f u v)) x y :=
  match x, y with
    | None, y => byComputing
    | Some x, None => byComputing
    | Some x, Some y => byComputing

theorem Option.mapMap3 ∀ (f: a → b → c → d) (g: d → r) (x: Option a) (y: Option b) (z: Option c):
    Option.map (Option.map3 f x y z) g = Option.map3 (u v w => g (f u v w)) x y z :=
  match x, y, z with
    | None, y, z => byComputing
    | Some x, None, z => byComputing
    | Some x, Some y, None => byComputing
    | Some x, Some y, Some z => byComputing

theorem Option.mapMap4 ∀ (f: a → b → c → d → e) (g: e → r) (x: Option a) (y: Option b) (z: Option c) (w: Option d):
    Option.map (Option.map4 f x y z w) g = Option.map4 (u v s t => g (f u v s t)) x y z w :=
  match x, y, z, w with
    | None, y, z, w => byComputing
    | Some x, None, z, w => byComputing
    | Some x, Some y, None, w => byComputing
    | Some x, Some y, Some z, None => byComputing
    | Some x, Some y, Some z, Some w => byComputing

--| With defaults for missing values, `map2` is `f` of the values or defaults,
--| when a default in either place makes `f` give the default result.
theorem Option.getOrElseMap2 ∀ (f: a → b → r) (da: a) (db: b) (d: r)
    (missing1: ∀ (y: b) => f da y = d)
    (missing2: ∀ (x: a) => f x db = d)
    (x: Option a) (y: Option b):
    Option.getOrElse (Option.map2 f x y) d = f (Option.getOrElse x da) (Option.getOrElse y db) :=
  match x, y with
    | None, y => (missing1 _).flipped
    | Some x, None => (missing2 _).flipped
    | Some x, Some y => byComputing

--| With defaults for missing values, `map3` is `f` of the values or defaults,
--| when a default in any place makes `f` give the default result.
theorem Option.getOrElseMap3 ∀ (f: a → b → c → r) (da: a) (db: b) (dc: c) (d: r)
    (missing1: ∀ (y: b) (z: c) => f da y z = d)
    (missing2: ∀ (x: a) (z: c) => f x db z = d)
    (missing3: ∀ (x: a) (y: b) => f x y dc = d)
    (x: Option a) (y: Option b) (z: Option c):
    Option.getOrElse (Option.map3 f x y z) d
      = f (Option.getOrElse x da) (Option.getOrElse y db) (Option.getOrElse z dc) :=
  match x, y, z with
    | None, y, z => (missing1 _ _).flipped
    | Some x, None, z => (missing2 _ _).flipped
    | Some x, Some y, None => (missing3 _ _).flipped
    | Some x, Some y, Some z => byComputing

--| With defaults for missing values, `map4` is `f` of the values or defaults,
--| when a default in any place makes `f` give the default result.
theorem Option.getOrElseMap4 ∀ (f: a → b → c → e → r) (da: a) (db: b) (dc: c) (de: e) (d: r)
    (missing1: ∀ (y: b) (z: c) (w: e) => f da y z w = d)
    (missing2: ∀ (x: a) (z: c) (w: e) => f x db z w = d)
    (missing3: ∀ (x: a) (y: b) (w: e) => f x y dc w = d)
    (missing4: ∀ (x: a) (y: b) (z: c) => f x y z de = d)
    (x: Option a) (y: Option b) (z: Option c) (w: Option e):
    Option.getOrElse (Option.map4 f x y z w) d
      = f (Option.getOrElse x da) (Option.getOrElse y db) (Option.getOrElse z dc) (Option.getOrElse w de) :=
  match x, y, z, w with
    | None, y, z, w => (missing1 _ _ _).flipped
    | Some x, None, z, w => (missing2 _ _ _).flipped
    | Some x, Some y, None, w => (missing3 _ _ _).flipped
    | Some x, Some y, Some z, None => (missing4 _ _ _).flipped
    | Some x, Some y, Some z, Some w => byComputing

--| `Option.decEq` on two `Some`s gives the values' answer, wrapped by
--| `Option.decSome`, so `==` on them is `==` on the values.
theorem Option.someBeqSome ∀ [auto eq: DecEq a] (x y: a): (Some x == Some y) = (x == y) := byComputing

theorem Option.someBeqSomeExample ∀ (x: Char): (Some x == Some 'A') = (x == 'A') := Option.someBeqSome x 'A'

--| `orElse` is `Some v` when the first option is, or when the first is `None`
--| and the second is.
theorem Option.orElseEqSome ∀ (y: Option a) (v: a) (x: Option a)
    (h: Option.orElse x y = Some v):
    (x = Some v) ∨ ((x = None) ∧ (y = Some v)) :=
  match x with
    | Some w => Inl h
    | None => Inr (Both byComputing h)

theorem Option.orElseNone ∀ (x: Option a): Option.orElse x None = x := match x with
  | Some w => byComputing
  | None => byComputing

theorem Option.orElseSome ∀ (v: a) (y: Option a): Option.orElse (Some v) y = Some v := byComputing

theorem Option.noneOrElse ∀ (y: Option a): Option.orElse None y = y := byComputing

--| `getOr` on a `Some` gives the value, whatever the fallback.
theorem Option.getOrSome ∀ (x fallback: a): Option.getOr (Some x) fallback = x := byComputing

--| `getOr` on a `None` gives the fallback.
theorem Option.getOrNone ∀ (fallback: a): Option.getOr (None: Option a) fallback = fallback := byComputing

--| If `map f x` is `Some v`, then `x` held some `u` with `f u = v`.
theorem Option.mapEqSome [goal: Prop]:
    ∀ (x: Option a) (f: a → b) (v: b) => Option.map x f = Some v
      → ∀ (cont: ∀ (u: a) => x = Some u → f u = v → goal) => goal
  | Some u, f, v, h, use => use u byComputing (Option.someInjective h)
  | None, f, v, h, use => (Option.noneNotSome v h).impossible

--| `map f x` is `None` exactly when `x` is.
theorem Option.mapEqNone ∀ (x: Option a) (f: a → b): Option.map x f = None ↔ x = None := match x with
  | Some u =>
    { forward = h => Void.impossible (Option.someNotNone (f u) h), backward = h => (Option.someNotNone u h).impossible }
  | None => { forward = h => byComputing, backward = h => byComputing }

theorem Option.mapEqNoneExample ∀ (x: Option Nat) (h: Option.map x Succ = None): x = None :=
  (Option.mapEqNone x Succ).forward h

--| If `flatMap f x` is `Some v`, then `x` held some `u` with `f u = Some v`.
theorem Option.flatMapEqSome [goal: Prop]:
    ∀ (x: Option a) (f: a → Option b) (v: b) => Option.flatMap x f = Some v
      → ∀ (cont: ∀ (u: a) => x = Some u → f u = Some v → goal) => goal
  | Some u, f, v, h, use => use u byComputing h
  | None, f, v, h, use => (Option.noneNotSome v h).impossible

--| If `filter p x` is `Some v`, then `x` is `Some v` and `p v` holds.
theorem Option.filterEqSome ∀ (x: Option a) (p: a → Bool) [v: a]
    (h: Option.filter x p = Some v):
    (x = Some v) ∧ (p v = True) :=
  match x with
    | Some u =>
      match e: p u with
        | True => Both h (Eq.trans (Eq.cong p (Option.someInjective h).flipped) e)

--| What `filter` drops: nothing, or something that failed the test.
theorem Option.filterEqNone ∀ (x: Option a) (p: a → Bool)
    (h: Option.filter x p = None):
    (x = None) ∨ (∃ (v: a) => (x = Some v) ∧ (p v = False)) :=
  match x with
    | None => Inl byComputing
    | Some u =>
      match e: p u with
        | False => Inr (Witness u (Both byComputing e))

--| `orElse` of an option with itself is the option.
theorem Option.orElseSelf ∀ (x: Option a): Option.orElse x x = x := match x with
  | Some w => byComputing
  | None => byComputing

--| If `alignWith` is `Some v`, `v` came from one of the three arms: the left
--| value alone, the right alone, or both.
theorem Option.alignWithEqSome ∀ [goal: Prop] (left: a → c) (right: b → c) (both: a → b → c) (v: c):
    ∀ (x: Option a) (y: Option b) => Option.alignWith x y left right both = Some v
      → ∀ (onLeft: ∀ (u: a) => x = Some u → y = None → left u = v → goal) (onRight: ∀ (w: b) => x = None
        → y = Some w
        → right w = v
        → goal) (onBoth: ∀ (u: a) (w: b) => x = Some u → y = Some w → both u w = v → goal) => goal
  | Some u, Some w, h, onLeft, onRight, onBoth => onBoth u w byComputing byComputing (Option.someInjective h)
  | Some u, None, h, onLeft, onRight, onBoth => onLeft u byComputing byComputing (Option.someInjective h)
  | None, Some w, h, onLeft, onRight, onBoth => onRight w byComputing byComputing (Option.someInjective h)
  | None, None, h, onLeft, onRight, onBoth => (Option.noneNotSome v h).impossible

--| A property each arm of `alignWith` gives, its result has.
theorem Option.alignWithHolds ∀ (q: c → Prop) (left: a → c) (right: b → c) (both: a → b → c)
    (onLeft: ∀ (u: a) => q (left u)) (onRight: ∀ (w: b) => q (right w)) (onBoth: ∀ (u: a) (w: b) => q (both u w))
    (x: Option a) (y: Option b) (v: c)
    (h: Option.alignWith x y left right both = Some v):
    q v :=
  Option.alignWithEqSome
    [goal := q v]
    left
    right
    both
    v
    x
    y
    h
    (u ex ey e => rewrite <- e then onLeft u)
    (w ex ey e => rewrite <- e then onRight w)
    (u w ex ey e => rewrite <- e then onBoth u w)

--| `alignWith` is `None` exactly when both options are.
theorem Option.alignWithEqNone ∀ (left: a → c) (right: b → c) (both: a → b → c) (x: Option a) (y: Option b):
    Option.alignWith x y left right both = None ↔ (x = None) ∧ (y = None) :=
  match x, y with
    | Some u, Some w => {
      forward = h => Void.impossible (Option.someNotNone (both u w) h),
      backward = h => (Option.someNotNone u h.left).impossible
    }
    | Some u, None => {
      forward = h => Void.impossible (Option.someNotNone (left u) h),
      backward = h => (Option.someNotNone u h.left).impossible
    }
    | None, Some w => {
      forward = h => Void.impossible (Option.someNotNone (right w) h),
      backward = h => (Option.someNotNone w h.right).impossible
    }
    | None, None => { forward = h => Both byComputing byComputing, backward = h => byComputing }

theorem Option.alignWithHoldsExample ∀ (x y: Option Nat) (v: Nat)
    (h: Option.alignWith x y Succ Succ (u w => Succ (u + w)) = Some v):
    v ≠ 0 :=
  Option.alignWithHolds
    (n => n ≠ 0)
    Succ
    Succ
    (u w => Succ (u + w))
    (u => Nat.succNotZero u)
    (w => Nat.succNotZero w)
    (u w => Nat.succNotZero (u + w))
    x
    y
    v
    h

--| `MkPair` is injective: equal pairs have equal parts.
theorem Pair.mkInjectiveFst ∀ [x1: a] [y1: b] [x2: a] [y2: b] (h: MkPair x1 y1 = MkPair x2 y2): x1 = x2 :=
  Eq.cong Pair.fst h
theorem Pair.mkInjectiveSnd ∀ [x1: a] [y1: b] [x2: a] [y2: b] (h: MkPair x1 y1 = MkPair x2 y2): y1 = y2 :=
  Eq.cong Pair.snd h

--| `==` on two pairs is `==` on both parts.
theorem Pair.mkBeqMk ∀ [auto eqA: DecEq a] [auto eqB: DecEq b] (x1: a) (y1: b) (x2: a) (y2: b):
    ((x1, y1) == (x2, y2)) = (x1 == x2 ∧ y1 == y2) :=
  byComputing

--| Two optional values are alike when both are `None`, or both are `Some`
--| of alike values: what `next` and a `loop`'s step give.
@[noReceiver]
def Option.Alike (alike: a → b → Prop): Option a → Option b → Prop
  | Some x, Some y => alike x y
  | None, None => Unit
  | _, _ => Void
