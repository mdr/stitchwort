-- Generated equations for guarded arms (docs/proposals/pattern-guards.md §6):
-- a guarded arm's equation takes its condition as a hypothesis, and an arm
-- below it takes the hypothesis that the condition failed where the two
-- overlap.

-- One column. `clamp.eq1: n ≤ limit → clamp limit n = n`, and
-- `clamp.eq2: (n <= limit) = False → clamp limit n = limit`.
def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem clampBelow (limit n: Nat) (le: n ≤ limit): clamp limit n = n := clamp.eq1 limit n le

theorem clampAbove (limit n: Nat) (above: (n <= limit) = False): clamp limit n = limit := clamp.eq2 limit n above

-- Two columns, and a split below the guard: the second arm overlaps the
-- first only where `b` is 0, so its hypothesis says so.
def pick: Nat → Nat → Nat
  | a, b if a < b => b
  | a, 0 => a
  | _, _ => 0

theorem pickLess (a b: Nat) (less: a < b): pick a b = b := pick.eq1 a b less

theorem pickZero (a: Nat): pick a 0 = a := pick.eq2 a (rfl: (a < 0) = False)

-- The arm below overlaps where the second is `Succ`.
theorem pickOther (a b: Nat) (notLess: (a < Succ b) = False): pick a (Succ b) = 0 :=
  pick.eq3 a (Succ b) notLess (same => omega)

-- `if h: P` names the hypothesis; the arm below takes `¬P`.
def needsPositive (n: Nat) [auto h: n > 0]: Nat := n - 1

def predecessor: Nat → Nat
  | n if h: n > 0 => needsPositive n
  | _ => 0

theorem predecessorZero: predecessor 0 = 0 := predecessor.eq2 0 (positive => omega)

theorem predecessorPositive (n: Nat) (positive: n > 0): predecessor n = needsPositive n := predecessor.eq1 n positive

-- `&&` in a guard is the `Bool` the definition tests.
def between: Nat → Nat
  | n if 3 <= n && n <= 9 => n
  | _ => 0

theorem betweenInside (n: Nat) (inside: (3 <= n && n <= 9) = True): between n = n := between.eq1 n inside

-- An or-pattern with a guard: one equation for each alternative.
def vowelWeight (strict: Bool): Char → Nat
  | 'a' | 'e' if strict => 2
  | 'a' | 'e' => 1
  | _ => 0

theorem strictA: vowelWeight True 'a' = 2 := vowelWeight.eq1.or1 True rfl

theorem lenientE: vowelWeight False 'e' = 1 := vowelWeight.eq2.or2 False rfl

-- An indexed family below the guard.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def headOr (d: Nat): (n: Nat) → Vec Nat n → Nat
  | _, VCons x _ if x > 3 => x
  | _, VCons _ _ => d
  | _, VNil => d

theorem headOrSmall (d x n: Nat) (xs: Vec Nat n) (small: (4 <= x) = False): headOr d (Succ n) (VCons x xs) = d :=
  headOr.eq2 d n x xs small

-- A guard in a recursive definition: `countBig.induct` carries the
-- condition into the case of the arm that has it, and its failure into the
-- case below.
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMostLength (xs: List Nat): countBig xs ≤ xs.length :=
  countBig.induct (xs result => result ≤ xs.length)
    omega
    (x rest big atMost => omega)
    (rest x small atMost => omega)
    xs

theorem countBigCons (x: Nat) (rest: List Nat) (big: x > 3): countBig [x, ..rest] = countBig rest + 1 :=
  countBig.eq2 x rest big
