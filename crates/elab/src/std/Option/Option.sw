-- Helpers for `Option`. These were in the core (docs/proposals/prelude-slim.md
-- stage 3); only the text readers needed them there.

def Option.flatMap: Option a -> (f: a -> Option b) -> Option b
  | None, f => None
  | Some x, f => f x

def Option.map: Option a -> (f: a -> b) -> Option b
  | None, f => None
  | Some x, f => Some (f x)

-- Two maps are one map of the composite.
theorem Option.mapMap (f: a -> b) (g: b -> c): (x: Option a) -> Option.map (Option.map x f) g = Option.map x (y => g (f y))
  | None => rfl
  | Some y => rfl

-- `Some` is injective: equal `Some`s hold equal values.
theorem Option.someInjective (x: a) (y: a) (h: Some x = Some y): x = y := Eq.cong (.getOrElse x) h

-- Whether there is a value: `(Some 3).isSome` is `True`.
def Option.isSome: Option a -> Bool
  | None => False
  | Some x => True

-- Whether there is none: `None.isNone` is `True`.
def Option.isNone: Option a -> Bool
  | None => True
  | Some x => False

-- The first option if it is a `Some`, else the second: `x.orElse y`.
def Option.orElse: Option a -> Option a -> Option a
  | Some x, y => Some x
  | None, y => y

-- Combines two options of one type: a lone value stays, two values go through
-- `both`. `x.merge y (a b => a + b)` adds the values that are there, and is
-- `None` only when both are.
def Option.merge: Option a -> Option a -> (both: a -> a -> a) -> Option a
  | Some x, Some y, both => Some (both x y)
  | Some x, None, both => Some x
  | None, Some y, both => Some y
  | None, None, both => None

-- `merge` for two types: `left` and `right` turn a lone value into the result,
-- `both` combines two. `x.alignWith y f g h` is `None` only when both are.
def Option.alignWith: Option a -> Option b -> (left: a -> c) -> (right: b -> c) -> (both: a -> b -> c) -> Option c
  | Some x, Some y, left, right, both => Some (both x y)
  | Some x, None, left, right, both => Some (left x)
  | None, Some y, left, right, both => Some (right y)
  | None, None, left, right, both => None

-- Takes the option apart: `none` for `None`, else `some` of the value.
-- `x.fold 0 (v => v + 1)` is `0` for `None` and `v + 1` for `Some v`.
def Option.fold: Option a -> (none: b) -> (some: a -> b) -> b
  | None, none, some => none
  | Some x, none, some => some x

-- Whether there is a value and `p` holds for it (`None` is `False`).
def Option.exists: Option a -> (p: a -> Bool) -> Bool
  | None, p => False
  | Some x, p => p x

-- Whether `p` holds for the value, if any (`None` is `True`).
def Option.forall: Option a -> (p: a -> Bool) -> Bool
  | None, p => True
  | Some x, p => p x

-- Keeps the value only when `p` holds for it: `x |> .filter (v => v > 2)`.
def Option.filter: Option a -> (p: a -> Bool) -> Option a
  | None, p => None
  | Some x, p => if p x then Some x else None

-- `orElse` is `Some v` when the first option is, or when the first is `None`
-- and the second is.
theorem Option.orElseEqSome (y: Option a) (v: a): (x: Option a) -> Option.orElse x y = Some v -> Or (x = Some v) (And (x = None) (y = Some v))
  | Some w, h => Inl h
  | None, h => Inr (Both rfl h)

theorem Option.orElseNone: (x: Option a) -> Option.orElse x None = x
  | Some w => rfl
  | None => rfl

theorem Option.orElseSome (v: a) (y: Option a): Option.orElse (Some v) y = Some v := rfl

theorem Option.noneOrElse (y: Option a): Option.orElse None y = y := rfl

-- If `map f x` is `Some v`, then `x` held some `u` with `f u = v`.
theorem Option.mapEqSome [goal: Prop]: (x: Option a) -> (f: a -> b) -> (v: b) -> Option.map x f = Some v -> ((u: a) -> x = Some u -> f u = v -> goal) -> goal
  | Some u, f, v, h, use => use u rfl (Option.someInjective (f u) v h)
  | None, f, v, h, use => Void.exfalso (Option.noneNotSome v h)

-- If `flatMap f x` is `Some v`, then `x` held some `u` with `f u = Some v`.
theorem Option.flatMapEqSome [goal: Prop]: (x: Option a) -> (f: a -> Option b) -> (v: b) -> Option.flatMap x f = Some v -> ((u: a) -> x = Some u -> f u = Some v -> goal) -> goal
  | Some u, f, v, h, use => use u rfl h
  | None, f, v, h, use => Void.exfalso (Option.noneNotSome v h)

-- If `filter p x` is `Some v`, then `x` is `Some v` and `p v` holds.
theorem Option.filterEqSome: (x: Option a) -> (p: a -> Bool) -> (v: a) -> Option.filter x p = Some v -> And (x = Some v) (p v = True)
  | Some u, p, v, h =>
    match e: p u with
      | True => Both h (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective u v h))) e)
      | False => Void.exfalso (Option.noneNotSome v h)
  | None, p, v, h => Void.exfalso (Option.noneNotSome v h)

-- `MkPair` is injective: equal pairs have equal parts.
theorem Pair.mkInjectiveFst (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): x1 = x2 := Eq.cong Pair.fst h
theorem Pair.mkInjectiveSnd (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): y1 = y2 := Eq.cong Pair.snd h

test "Option.isSome" := (Some 1).isSome == True && (None: Option Nat).isSome == False
test "Option.isNone" := (Some 1).isNone == False && (None: Option Nat).isNone == True
test "Option.orElse" := (Some 1).orElse (Some 2) == Some 1 && (None: Option Nat).orElse (Some 2) == Some 2 && (None: Option Nat).orElse None == None
test "Option.orElse chain" := ((None: Option Nat).orElse None |> .orElse (Some 3)) == Some 3
test "Option.merge" := (Some 1).merge (Some 2) (+) == Some 3
test "Option.merge lone" := (Some 1).merge None (+) == Some 1 && (None: Option Nat).merge (Some 2) (+) == Some 2
test "Option.merge none" := (None: Option Nat).merge None (+) == None
test "Option.alignWith" := (Some 1).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 5
test "Option.alignWith lone" := (Some 1).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == Some 11 && (None: Option Nat).alignWith (Some 5) (+ 10) (+ 20) (*) == Some 25
test "Option.alignWith none" := (None: Option Nat).alignWith (None: Option Nat) (+ 10) (+ 20) (*) == None
test "Option.fold" := (Some 4).fold 0 (+ 1) == 5 && (None: Option Nat).fold 0 (+ 1) == 0
test "Option.exists" := (Some 3).exists (> 2) == True && (Some 1).exists (> 2) == False && (None: Option Nat).exists (> 2) == False
test "Option.forall" := (Some 3).forall (> 2) == True && (Some 1).forall (> 2) == False && (None: Option Nat).forall (> 2) == True
test "Option.filter" := (Some 3).filter (> 2) == Some 3 && (Some 1).filter (> 2) == None && (None: Option Nat).filter (> 2) == None
test "Option.filter in a pipe" := (Some 3 |> .filter (> 2)) == Some 3
