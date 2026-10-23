-- Automatic proofs, decision procedures, `if`, and division.

import Std (Bool, Void)

-- `/` needs a proof that the divisor isn't zero. For a literal, `auto`
-- decides it at compile time.
def half (n: Nat): Nat := n / 2

theorem sevenHalves: 7 / 2 = 3 := rfl

theorem sevenMod: 7 % 2 = 1 := rfl

-- For a divisor only known at runtime, establish it first: inside the `then`
-- branch, `h: d != 0` is in scope, and `auto` finds it.
def safeDiv (n: Nat) (d: Nat): Nat := if h: d != 0 then n / d else 0

theorem safeDivByZero: safeDiv 5 0 = 0 := rfl

theorem safeDivWorks: safeDiv 9 3 = 3 := rfl

-- A function can ask for a proof itself, and its callers' `auto` provides it.
def average (total: Nat) (count: Nat): [auto ok: count != 0] -> Nat := total / count

def averageOfThree: Nat := average 12 3

-- A hypothesis can also be passed on explicitly, by name.
def averageOrZero (total: Nat) (count: Nat): Nat :=
  if h: count != 0 then average total count [ok := h] else 0

-- Comparisons are propositions, decided by computation.
theorem twoBelowThree: 2 < 3 := rfl

-- `get` needs a proof that the index is in range.
def get: (xs: List a) -> (i: Nat) -> [auto ok: i < xs.length] -> a
  | Cons x xs, Zero => x
  | Cons x xs, Succ i => get xs i
  -- When the list is empty, `ok: i < List.length Nil` computes to `False = True`,
  -- which is impossible.
  | Nil, i => Void.absurd (Bool.falseNotTrue ok)

def secondOfThree: Nat := get [10, 20, 30] 1

theorem secondIsTwenty: secondOfThree = 20 := rfl
