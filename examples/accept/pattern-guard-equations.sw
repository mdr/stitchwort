-- Generated equations for guarded arms (docs/proposals/pattern-guards.md §6):
-- a guarded arm's equation takes its condition as a hypothesis, and an arm
-- below it takes the hypothesis that the condition failed where the two
-- overlap.
import Std (Bool, DecEq)

-- One column. `clamp.eq1: (n <= limit) = True → clamp limit n = n` (shown
-- `n ≤ limit`), and `clamp.eq2: (n <= limit) = False → clamp limit n = limit`.
def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem clampBelow ∀ (limit n: Nat) (le: n ≤ limit): clamp limit n = n := clamp.eq1 limit n le

theorem clampAbove ∀ (limit n: Nat) (above: (n <= limit) = False): clamp limit n = limit := clamp.eq2 limit n above

-- Two columns, and a split below the guard: the second arm overlaps the
-- first only where `b` is 0, so its hypothesis says so.
def pick: Nat → Nat → Nat
  | a, b if a < b => b
  | a, 0 => a
  | _, _ => 0

theorem pickLess ∀ (a b: Nat) (less: a < b): pick a b = b := pick.eq1 a b less

theorem pickZero ∀ (a: Nat): pick a 0 = a := pick.eq2 a (byComputing: (a < 0) = False)

-- The arm below overlaps where the second is `Succ`.
theorem pickOther ∀ (a b: Nat) (notLess: (a < Succ b) = False): pick a (Succ b) = 0 :=
  pick.eq3 a (Succ b) notLess (same => arithmetic)

-- A condition written as a proposition (`!=` is `≠`) is stated as itself,
-- though the definition tests its `Bool`: `skipThree.eq1` takes `n ≠ 3`, and
-- `skipThree.eq2` `n = 3` (`¬(n ≠ 3)`, where the proposition is an
-- equation's negation).
def skipThree: Nat → Nat
  | n if n != 3 => n
  | _ => 0

theorem skipThreeOther ∀ (n: Nat) (other: n ≠ 3): skipThree n = n := skipThree.eq1 n other

theorem skipThreeThree: skipThree 3 = 0 := skipThree.eq2 3 byComputing

-- `==` is a `Bool`: `emptyOrOne.eq1` takes `(xs == []) = True` and
-- `emptyOrOne.eq2` `(xs == []) = False` (D3699). Written as the
-- proposition, `xs = []`, it is stated as `xs = []` and `xs ≠ []`.
def emptyOrOne: List Nat → Nat
  | xs if xs == [] => 0
  | _ => 1

theorem emptyOrOneEmpty ∀ (xs: List Nat) (empty: (xs == []) = True): emptyOrOne xs = 0 := emptyOrOne.eq1 xs empty

theorem emptyOrOneNot ∀ (xs: List Nat) (notEmpty: (xs == []) = False): emptyOrOne xs = 1 := emptyOrOne.eq2 xs notEmpty

def emptyOrTwo: List Nat → Nat
  | xs if xs = [] => 0
  | _ => 2

theorem emptyOrTwoEmpty ∀ (xs: List Nat) (empty: xs = []): emptyOrTwo xs = 0 := emptyOrTwo.eq1 xs empty

theorem emptyOrTwoNot ∀ (xs: List Nat) (notEmpty: xs ≠ []): emptyOrTwo xs = 2 := emptyOrTwo.eq2 xs notEmpty

-- `if h: P` names the hypothesis; the arm below takes `¬P`.
def needsPositive (n: Nat) [auto h: n > 0]: Nat := n - 1

def predecessor: Nat → Nat
  | n if h: n > 0 => needsPositive n
  | _ => 0

theorem predecessorZero: predecessor 0 = 0 := predecessor.eq2 0 (positive => arithmetic)

theorem predecessorPositive ∀ (n: Nat) (positive: n > 0): predecessor n = needsPositive n := predecessor.eq1 n positive

-- `&&` in a guard is a `Bool` like any other, not split (D3699):
-- `between.eq1: (3 <= n && n <= 9) = True → between n = n`,
-- `between.eq2: (3 <= n && n <= 9) = False → between n = 0`. The
-- conjunction is `.read` away.
def between: Nat → Nat
  | n if 3 <= n && n <= 9 => n
  | _ => 0

theorem betweenInside ∀ (n: Nat) (inside: 3 ≤ n ∧ n ≤ 9): between n = n :=
  between.eq1 n (Bool.andIntro inside.left inside.right)

theorem betweenOutside ∀ (n: Nat) (outside: (3 <= n && n <= 9) = False): between n = 0 := between.eq2 n outside

-- An or-pattern with a guard: one equation for each alternative.
def vowelWeight (strict: Bool): Char → Nat
  | 'a' | 'e' if strict => 2
  | 'a' | 'e' => 1
  | _ => 0

theorem strictA: vowelWeight True 'a' = 2 := vowelWeight.eq1.or1 True byComputing

theorem lenientE: vowelWeight False 'e' = 1 := vowelWeight.eq2.or2 False byComputing

-- An indexed family below the guard.
type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def headOr (d: Nat): (n: Nat) → Vec Nat n → Nat
  | _, VCons x _ if x > 3 => x
  | _, VCons _ _ => d
  | _, VNil => d

theorem headOrSmall ∀ (d x n: Nat) (xs: Vec Nat n) (small: (4 <= x) = False): headOr d (Succ n) (VCons x xs) = d :=
  headOr.eq2 d n x xs small

-- A guard in a recursive definition: `countBig.induct` carries the
-- condition into the case of the arm that has it, and its failure into the
-- case below.
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMostLength ∀ (xs: List Nat): countBig xs ≤ xs.length :=
  countBig.induct
    (xs result => result ≤ xs.length)
    arithmetic
    (x rest big atMost => arithmetic)
    (rest x small atMost => arithmetic)
    xs

theorem countBigCons ∀ (x: Nat) (rest: List Nat) (big: x > 3): countBig [x, ..rest] = countBig rest + 1 :=
  countBig.eq2 x rest big

-- A `decreasing` definition with a guarded arm: its equations go through
-- `f.unfold`.
def countDown (n: Nat): Bool → Nat
    decreasing n
  | flag if n > 0 => 1 + countDown (n - 1) flag [decreasing := arithmetic]
  | _ => 0

theorem countDownStep ∀ (n: Nat) (flag: Bool) (positive: n > 0): countDown n flag = countDown (n - 1) flag + 1 :=
  countDown.eq1 n flag positive

theorem countDownIsN ∀ (n: Nat) (flag: Bool): countDown n flag = n :=
  countDown.induct
    (n flag result => result = n)
    (n flag positive below => arithmetic)
    (n flag notPositive => arithmetic)
    n
    flag

-- The arm below takes the failure in the same form, `(1 <= n) = False`,
-- though this definition tests `n > 0` by `Decidable.elim` (its recursive
-- call needs the proof).
theorem countDownBelow ∀ (n: Nat) (flag: Bool) (small: (1 <= n) = False): countDown n flag = 0 :=
  countDown.eq2 n flag small

-- A conjunction of three, with propositions among its sides: still the
-- `Bool`, `= True` and `= False`, in the equations and `f.induct`'s cases.
def countSome: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x != 0 && x > 1 && x != 7 => 1 + countSome rest
  | [_, ..rest] => countSome rest

theorem countSomeAtMostLength ∀ (xs: List Nat): countSome xs ≤ xs.length :=
  countSome.induct
    (xs result => result ≤ xs.length)
    arithmetic
    (x rest all atMost => arithmetic)
    (head rest not atMost => arithmetic)
    xs

theorem countSomeStep ∀ (x: Nat) (rest: List Nat)
    (nonzero: x ≠ 0)
    (big: x > 1)
    (notSeven: x ≠ 7):
    countSome [x, ..rest] = 1 + countSome rest :=
  countSome.eq2 x rest (Bool.andIntro (DecEq.trueOfNe nonzero) (Bool.andIntro big (DecEq.trueOfNe notSeven)))

-- A negated equation fails as the equation: `drop3.eq2` takes `head = 3`.
def drop3: List Nat → List Nat
  | [] => []
  | [x, ..rest] if x != 3 => [x, ..drop3 rest]
  | [_, ..rest] => drop3 rest

theorem drop3Three ∀ (rest: List Nat): drop3 [3, ..rest] = drop3 rest := drop3.eq3 3 rest byComputing

theorem drop3NoLonger ∀ (xs: List Nat): (drop3 xs).length ≤ xs.length :=
  drop3.induct
    (xs result => result.length ≤ xs.length)
    arithmetic
    (x rest ne atMost => arithmetic)
    (head rest eq atMost => arithmetic)
    xs
