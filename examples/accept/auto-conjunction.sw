-- The branch of an `if p && q` knows `p ∧ q`, and `auto` uses each part of a
-- conjunction in scope, so `rem` (which needs `b ≠ 0`) finds its proof from
-- either side. The conjunction may be written `&&` or `∧`, nested, or come
-- from a guard; a `Bool` operand is known to be `True`.

import Std (Nat)

def rem (a b: Nat) [auto ok: b ≠ 0]: Nat := a % b

def modBoth (a b c: Nat): Nat := if b != 0 && c != 0 then rem a b else 0

test "both nonzero" := modBoth 7 3 1 == 1

test "second zero" := modBoth 7 3 0 == 0

def modBothProp (a b c: Nat): Nat := if b ≠ 0 ∧ c ≠ 0 then rem a b else 0

test "both nonzero, proposition" := modBothProp 7 3 1 == 1

test "first zero, proposition" := modBothProp 7 0 1 == 0

-- The middle of three.
def modMiddle (a b c d: Nat): Nat := if b != 0 && (c != 0 && d != 0) then rem a c else 0

test "middle nonzero" := modMiddle 7 3 5 1 == 2

test "middle zero" := modMiddle 7 3 0 1 == 0

def modLast (a b c d: Nat): Nat := if b != 0 && c != 0 && d != 0 then rem a d else 0

test "last nonzero" := modLast 7 3 5 4 == 3

test "last zero" := modLast 7 3 5 0 == 0

-- `b ≠ 0` from the part `b > 0`.
def modPositive (a b c: Nat): Nat := if b > 0 && c > 0 then rem a b else 0

test "both positive" := modPositive 7 4 2 == 3

test "not positive" := modPositive 7 0 2 == 0

-- A `Bool` beside a proposition.
def modIf (wanted: Bool) (a b: Nat): Nat := if wanted && b != 0 then rem a b else a

test "wanted" := modIf True 7 4 == 3 ∧ modIf False 7 4 == 7 ∧ modIf True 7 0 == 7

-- An `if` inside an `if`: each branch knows its own conjunction and the
-- outer one.
def modNested (a b c d: Nat): Nat :=
  if b != 0 && c != 0 then if d != 0 && a > b then rem (rem a b) d + rem a c else rem a c else 0

test "nested" := modNested 7 3 5 4 == 3 ∧ modNested 7 3 5 0 == 2 ∧ modNested 7 0 5 4 == 0

-- A guard on a conjunction.
def modGuard: (Nat, Nat, Nat) → Nat
  | (a, x, y) if x != 0 && y != 0 => rem a x + rem a y
  | _ => 0

test "guard" := modGuard (7, 3, 4) == 4 ∧ modGuard (7, 3, 0) == 0

-- A conjunction given as a hypothesis.
def modGiven (a b c: Nat) (h: b ≠ 0 ∧ c ≠ 0): Nat := rem a b

test "given hypothesis" := modGiven 7 1 1 (Both (Nat.succNotZero 0) (Nat.succNotZero 0)) == 0
