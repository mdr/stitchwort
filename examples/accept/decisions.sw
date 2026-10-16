-- Automatic proofs, decision procedures, `if`, and division.

-- `/` needs a proof that the divisor isn't zero. For a literal, `auto`
-- decides it at compile time.
half : Nat -> Nat
half n = n / 2

theorem sevenHalves : 7 / 2 = 3
sevenHalves = rfl

theorem sevenMod : 7 % 2 = 1
sevenMod = rfl

-- For a divisor only known at runtime, establish it first: inside the `then`
-- branch, `h : d != 0` is in scope, and `auto` finds it.
safeDiv : Nat -> Nat -> Nat
safeDiv n d = if h : d != 0 then n / d else 0

theorem safeDivByZero : safeDiv 5 0 = 0
safeDivByZero = rfl

theorem safeDivWorks : safeDiv 9 3 = 3
safeDivWorks = rfl

-- A function can ask for a proof itself, and its callers' `auto` provides it.
average : (total : Nat) -> (count : Nat) -> [auto ok : count != 0] -> Nat
average total count = total / count

averageOfThree : Nat
averageOfThree = average 12 3

-- A hypothesis can also be passed on explicitly, by name.
averageOrZero : Nat -> Nat -> Nat
averageOrZero total count =
  if h : count != 0 then average total count [ok := h] else 0

-- Comparisons are propositions, decided by computation.
theorem twoBelowThree : 2 < 3
twoBelowThree = rfl

-- `get` needs a proof that the index is in range.
get : (xs : List a) -> (i : Nat) -> [auto ok : i < List.length xs] -> a
get (Cons x xs) Zero     = x
get (Cons x xs) (Succ i) = get xs i
-- When the list is empty, `ok : i < List.length Nil` computes to `False = True`,
-- which is impossible.
get Nil         i        = Void.absurd (Bool.falseNotTrue ok)

secondOfThree : Nat
secondOfThree = get [10, 20, 30] 1

theorem secondIsTwenty : secondOfThree = 20
secondIsTwenty = rfl
