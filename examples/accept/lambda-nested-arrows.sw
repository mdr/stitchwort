-- A curried lambda written with nested arrows, `r => p => …`, is the same
-- function as `r p => …`, also with no expected type, as when it is bound
-- by `let`: its parameters' types come from its body or its uses (SW-910).

import Std (Fail)

def roll (sides: Nat): Nat := sides + 1

-- The body fixes both parameters' types.
test "let, fixed by the body" :=
  let nested := n => m => roll n + roll m
  let flat := n m => roll n + roll m
  nested 1 2 == 5 ∧ flat 1 2 == 5

-- The uses fix both parameters' types.
test "let, fixed by the use" :=
  let nested := x => y => x + y
  let flat := x y => x + y
  nested 2 3 == 5 ∧ flat 2 3 == 5

-- Three parameters, and the two forms mixed.
test "let, three parameters" :=
  let nested := a => b => c => a + b + c
  let mixed := a b => c => a + b + c
  nested 1 2 3 == 6 ∧ mixed 1 2 3 == 6

-- A body that may fail: a function returning a computation, either way.
def checkedNested (base: Nat): {Fail} Nat :=
  let span := lo => hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  span base 3 + span 2 5

def checkedFlat (base: Nat): {Fail} Nat :=
  let span := lo hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  span base 3 + span 2 5

test "let, with effects" :=
  Fail.toResult (() => checkedNested 1) == Ok 5 ∧ Fail.toResult (() => checkedFlat 1) == Ok 5

def apply2 (f: Nat → Nat → Nat) (a: Nat) (b: Nat): Nat := f a b

def applyAny [a: Type] [b: Type] [c: Type] (f: a → b → c) (x: a) (y: b): c := f x y

-- As an argument, where the parameter's type is known.
test "argument, known type" :=
  apply2 (x => y => x + y) 2 3 == 5 ∧ apply2 (x y => x + y) 2 3 == 5

-- As an argument whose types the later arguments fix.
test "argument, unknown type" :=
  applyAny (x => y => x + y) 2 3 == 5 ∧ applyAny (x y => x + y) 2 3 == 5
