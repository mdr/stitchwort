-- Helpers for `Option`: `map`, `flatMap`, `orElse`, `merge`, `map2` and the
-- like. Their lemmas are in Option/Lemmas.sw.

def Option.flatMap: Option a → (f: a → Option b) → Option b
  | None, f => None
  | Some x, f => f x

def Option.map: Option a → (f: a → b) → Option b
  | None, f => None
  | Some x, f => Some (f x)

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

-- Takes the option apart: `none` for `None`, else `some` of the value.
-- `x.fold 0 (v => v + 1)` is `0` for `None` and `v + 1` for `Some v`.
-- `none` is an argument, so one that performs runs whatever `x` is:
-- `x.fold (Fail.fail message) (v => v)` always fails, where
-- `Fail.need x message` fails only for `None`.
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
