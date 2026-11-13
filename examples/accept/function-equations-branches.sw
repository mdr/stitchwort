-- Branch equations (docs/proposals/function-equations.md, stage 1b): below
-- each arm, every way through the `if`s and `match`es in tail position gets
-- `f.eqK.ifTrue`, `.ifFalse`, `.some`, `.alt2`, ... with the condition (or
-- the matched pattern) as a hypothesis. Each is an ordinary theorem.
import Std (Bool, Eq, Fin, List, Nat, Option, Void)

-- A `Bool` `if`: `h1: 3 < x` and `h1: (3 < x) = False`.
def big: List Nat → Nat
  | [] => 0
  | [x, ..rest] => if 4 ≤ x then x else big rest

theorem bigHit ∀ (x: Nat) (rest: List Nat) (h: 3 < x): big [x, ..rest] = x :=
  big.eq2.ifTrue x rest h

theorem bigMiss ∀ (x: Nat) (rest: List Nat) (h: (3 < x) = False): big [x, ..rest] = big rest :=
  big.eq2.ifFalse x rest h

-- The call is stuck on `x`, so `rewrite` finds it.
theorem bigAtMostRest ∀ (x: Nat) (rest: List Nat) (h: (3 < x) = False): big [x, ..rest] ≤ big rest :=
  rewrite big.eq2.ifFalse x rest h in omega

-- `if h: b = False`: the `else` is the complement equation, `notFresh: b = True`.
def countFresh: List Bool → Nat
  | [] => 0
  | [b, ..rest] => if fresh: b = False then 1 + countFresh rest else countFresh rest

theorem countFreshTrue ∀ (rest: List Bool): countFresh [True, ..rest] = countFresh rest :=
  countFresh.eq2.ifFalse True rest rfl

theorem countFreshStep ∀ (b: Bool) (rest: List Bool) (fresh: b = False):
    countFresh [b, ..rest] = 1 + countFresh rest :=
  countFresh.eq2.ifTrue b rest fresh

-- `if h: p` whose branch uses `h`: `h` is in the statement.
def check (n: Nat) (i: Nat): Option (Fin n) := if h: i < n then Some (Fin.ofNatLt n i h) else None

theorem checkIn ∀ (n: Nat) (i: Nat) (h: i < n): check n i = Some (Fin.ofNatLt n i h) :=
  check.eq.ifTrue n i h

theorem checkOut ∀ (n: Nat) (i: Nat) (h: ¬(i < n)): check n i = None := check.eq.ifFalse n i h

-- `decreasing`: the equations are proved through `gcd.unfold`.
def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

theorem gcdZero ∀ (a: Nat): gcd a 0 = a := gcd.eq.ifTrue a 0 rfl

-- A `match` on an expression: `isSome`, `isNone`.
def headOr (d: Nat) (xs: List Nat): Nat := match List.head xs with
  | Some x => x
  | None => d

theorem headOrNil ∀ (d: Nat): headOr d [] = d := headOr.eq.none d [] rfl

theorem headOrSome ∀ (d: Nat) (xs: List Nat) (x: Nat) (found: List.head xs = Some x): headOr d xs = x :=
  headOr.eq.some d xs x found

-- A `match` on a variable of the arm, compiled into the case tree: its
-- patterns go into the left side.
def takeFirst [a: Type] (xs: List a): Nat → List a
  | Zero => []
  | Succ k =>
    match xs with
      | [] => []
      | [x, ..rest] => [x, ..takeFirst rest k]

theorem takeCons ∀ [a: Type] (k: Nat) (x: a) (rest: List a):
    takeFirst [x, ..rest] (Succ k) = [x, ..takeFirst rest k] :=
  takeFirst.eq2.cons k x rest

-- A catch-all after an overlapping alternative: `notAlt1`.
def both (a: Option Nat) (b: Option Nat): Nat := match (a, b) with
  | (Some x, Some y) => x + y
  | _ => 0

theorem bothNone ∀ (b: Option Nat): both None b = 0 := both.eq.alt2 None b cases

theorem bothSome ∀ (x: Nat) (y: Nat): both (Some x) (Some y) = x + y :=
  both.eq.alt1 (Some x) (Some y) x y rfl

-- On several expressions, stated as on their tuple, `match (a, k + 1)`:
-- `isAlt1: (a, k + 1) = (Some x, Succ y)` (SW-1074).
def bothAfter (k: Nat) (a: Option Nat): Nat := match a, k + 1 with
  | Some x, Succ y => x + y
  | _, _ => 0

theorem bothAfterSome ∀ (k: Nat) (a: Option Nat) (x: Nat) (h: a = Some x): bothAfter k a = x + k :=
  bothAfter.eq.alt1 k a x k (rewrite h in rfl)

-- Nested: a `match` on the alternative's variable.
def firstTwo (xs: List Nat): Nat := match List.head xs with
  | Some x =>
    match x with
      | 0 => 1
      | Succ n => n
  | None => 0

theorem firstTwoSucc ∀ (xs: List Nat) (n: Nat) (found: List.head xs = Some (Succ n)): firstTwo xs = n :=
  firstTwo.eq.some.succ xs n found

-- §1.2's wall: a named `match` on a `Bool` whose branch uses the equation.
-- `rewrite`, `match` and `cases` can't prove these (E-REWRITE-MOTIVE,
-- E-MATCH-MOTIVE, E-CASES); the generated one-`J` proof can.
type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | [] => None
  | [x, ..rest] =>
    match big: Nat.leq 10 x with
      | True => Some { value = x, isBig = big }
      | False => firstBig rest

theorem firstBigHit ∀ (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig [x, ..rest] = Some { value = x, isBig = h } :=
  firstBig.eq2.true x rest h

theorem firstBigSkip ∀ (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = False):
    firstBig [x, ..rest] = firstBig rest :=
  firstBig.eq2.false x rest h
