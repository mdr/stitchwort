-- Helpers for `Option`. These were in the core (docs/proposals/prelude-slim.md
-- stage 3); only the text readers needed them there.

def Option.flatMap (f: a -> Option b): Option a -> Option b
  | None => None
  | Some x  => f x

def Option.map (f: a -> b): Option a -> Option b
  | None => None
  | Some x  => Some (f x)

-- `Some` is injective: equal `Some`s hold equal values.
theorem Option.someInjective (x: a) (y: a) (h: Some x = Some y): x = y := Eq.cong (Option.getOrElse x) h

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
  | None,   y => y

-- Combines two options of one type: a lone value stays, two values go through
-- `both`. `x.merge (a b => a + b) y` adds the values that are there, and is
-- `None` only when both are.
def Option.merge (both: a -> a -> a): Option a -> Option a -> Option a
  | Some x, Some y => Some (both x y)
  | Some x, None   => Some x
  | None,   Some y => Some y
  | None,   None   => None

-- `merge` for two types: `left` and `right` turn a lone value into the result,
-- `both` combines two. `x.alignWith f g h y` is `None` only when both are.
def Option.alignWith (left: a -> c) (right: b -> c) (both: a -> b -> c): Option a -> Option b -> Option c
  | Some x, Some y => Some (both x y)
  | Some x, None   => Some (left x)
  | None,   Some y => Some (right y)
  | None,   None   => None

-- Takes the option apart: `none` for `None`, else `some` of the value.
-- `x.fold 0 (v => v + 1)` is `0` for `None` and `v + 1` for `Some v`.
def Option.fold (none: b) (some: a -> b): Option a -> b
  | None => none
  | Some x => some x

-- Whether there is a value and `p` holds for it (`None` is `False`).
def Option.exists (p: a -> Bool): Option a -> Bool
  | None => False
  | Some x => p x

-- Whether `p` holds for the value, if any (`None` is `True`).
def Option.forall (p: a -> Bool): Option a -> Bool
  | None => True
  | Some x => p x

-- Keeps the value only when `p` holds for it: `x |> .filter (v => v > 2)`.
def Option.filter (p: a -> Bool): Option a -> Option a
  | None => None
  | Some x => if p x then Some x else None

-- `orElse` is `Some v` when the first option is, or when the first is `None`
-- and the second is.
theorem Option.orElseEqSome (y: Option a) (v: a): (x: Option a) -> Option.orElse x y = Some v -> Or (x = Some v) (And (x = None) (y = Some v))
  | Some w, h => Inl h
  | None,   h => Inr (Both rfl h)

theorem Option.orElseNone: (x: Option a) -> Option.orElse x None = x
  | Some w => rfl
  | None   => rfl

theorem Option.orElseSome (v: a) (y: Option a): Option.orElse (Some v) y = Some v := rfl

theorem Option.noneOrElse (y: Option a): Option.orElse None y = y := rfl

-- If `map f x` is `Some v`, then `x` held some `u` with `f u = v`.
theorem Option.mapEqSome [goal: Prop] (f: a -> b) (v: b): (x: Option a) -> Option.map f x = Some v -> ((u: a) -> x = Some u -> f u = v -> goal) -> goal
  | Some u, h, use => use u rfl (Option.someInjective (f u) v h)
  | None,   h, use => Void.exfalso (Option.noneNotSome v h)

-- If `flatMap f x` is `Some v`, then `x` held some `u` with `f u = Some v`.
theorem Option.flatMapEqSome [goal: Prop] (f: a -> Option b) (v: b): (x: Option a) -> Option.flatMap f x = Some v -> ((u: a) -> x = Some u -> f u = Some v -> goal) -> goal
  | Some u, h, use => use u rfl h
  | None,   h, use => Void.exfalso (Option.noneNotSome v h)

-- If `filter p x` is `Some v`, then `x` is `Some v` and `p v` holds.
theorem Option.filterEqSome (p: a -> Bool) (v: a): (x: Option a) -> Option.filter p x = Some v -> And (x = Some v) (p v = True)
  | Some u, h =>
    match e: p u with
      | True  => Both h (Eq.trans (Eq.cong p (Eq.sym (Option.someInjective u v h))) e)
      | False => Void.exfalso (Option.noneNotSome v h)
  | None,   h => Void.exfalso (Option.noneNotSome v h)

-- `MkPair` is injective: equal pairs have equal parts.
theorem Pair.mkInjectiveFst (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): x1 = x2 := Eq.cong Pair.fst h
theorem Pair.mkInjectiveSnd (x1: a) (y1: b) (x2: a) (y2: b) (h: MkPair x1 y1 = MkPair x2 y2): y1 = y2 := Eq.cong Pair.snd h

test "Option.isSome" := (Some 1).isSome == True && (None: Option Nat).isSome == False
test "Option.isNone" := (Some 1).isNone == False && (None: Option Nat).isNone == True
test "Option.orElse" := (Some 1).orElse (Some 2) == Some 1 && (None: Option Nat).orElse (Some 2) == Some 2 && (None: Option Nat).orElse None == None
test "Option.orElse chain" := ((None: Option Nat).orElse None |> .orElse (Some 3)) == Some 3
test "Option.merge" := (Some 1).merge (a b => a + b) (Some 2) == Some 3
test "Option.merge lone" := (Some 1).merge (a b => a + b) None == Some 1 && (None: Option Nat).merge (a b => a + b) (Some 2) == Some 2
test "Option.merge none" := (None: Option Nat).merge (a b => a + b) None == None
test "Option.alignWith" := (Some 1).alignWith (a => a + 10) (b => b + 20) (a b => a * b) (Some 5) == Some 5
test "Option.alignWith lone" := (Some 1).alignWith (a => a + 10) (b => b + 20) (a b => a * b) (None: Option Nat) == Some 11 && (None: Option Nat).alignWith (a => a + 10) (b => b + 20) (a b => a * b) (Some 5) == Some 25
test "Option.alignWith none" := (None: Option Nat).alignWith (a => a + 10) (b => b + 20) (a b => a * b) (None: Option Nat) == None
test "Option.fold" := (Some 4).fold 0 (v => v + 1) == 5 && (None: Option Nat).fold 0 (v => v + 1) == 0
test "Option.exists" := (Some 3).exists (v => v > 2) == True && (Some 1).exists (v => v > 2) == False && (None: Option Nat).exists (v => v > 2) == False
test "Option.forall" := (Some 3).forall (v => v > 2) == True && (Some 1).forall (v => v > 2) == False && (None: Option Nat).forall (v => v > 2) == True
test "Option.filter" := (Some 3).filter (v => v > 2) == Some 3 && (Some 1).filter (v => v > 2) == None && (None: Option Nat).filter (v => v > 2) == None
test "Option.filter in a pipe" := (Some 3 |> .filter (v => v > 2)) == Some 3
