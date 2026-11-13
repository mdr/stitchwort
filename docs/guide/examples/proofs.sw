-- Chapter 10: proofs.
import Std (Eq, Exists, Fail, Fin, Iff, Int, List, Nat, Option, Quot, Vec)
import Std.Exists (Witness)

-- begin rfl
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := rfl

theorem zeroPlus (n: Nat): 0 + n = n := rfl
-- end rfl

-- begin induction
theorem timesOne (n: Nat): n * 1 = n := match n with
  | Zero => rfl
  | Succ k => Eq.cong Succ (timesOne k)
-- end induction

-- begin lists
def mapList (f: a → b): List a → List b
  | [] => []
  | [x, ..rest] => [f x, ..mapList f rest]

theorem lengthMapList (f: a → b) (xs: List a): (mapList f xs).length = xs.length := match xs with
  | [] => rfl
  | [x, ..rest] => Eq.cong Succ (lengthMapList f rest)
-- end lists

-- begin rewrite
theorem swapTimesOne (a: Nat) (b: Nat): (a + b) * 1 = b + a :=
  rewrite Nat.mulOne (a + b), Nat.addComm a b
-- end rewrite

-- begin calc
theorem chain (a: Nat) (b: Nat) (c: Nat) (ab: a = b) (bc: b ≤ c) (small: c < 10): a < 10 :=
  calc a
    _ = b := ab
    _ ≤ c := bc
    _ < 10 := small
-- end calc

-- begin omega
theorem roomForOne (x: Nat) (y: Nat) (before: x < y) (limit: y ≤ 10): x + 1 ≤ 10 := omega

theorem twiceIsDouble (n: Nat): double n = 2 * n := omega

theorem stepBack (n: Nat) (x: Int) (h: x < n.toInt): x - 1 < n.toInt - 1 := omega

theorem thirdOfTriple (k: Int): (3 * k) / 3 = k := omega

theorem sizeOfSum (x: Int) (y: Int): (x + y).natAbs ≤ x.natAbs + y.natAbs := omega
-- end omega

-- begin omega-logic
def isNeighbour (a: Nat) (b: Nat): Bool := a + 1 == b || b + 1 == a

theorem neighboursDiffer (a: Nat) (b: Nat) (near: isNeighbour a b = True): a != b := omega

theorem nearZero (a: Nat) (h: a ≤ 1): a = 0 ∨ a = 1 := omega
-- end omega-logic

-- begin ring
theorem squareOfSum (a: Nat) (b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := ring

theorem areaGrows (w: Nat) (h: Nat): (w + 1) * (h + 1) = w * h + w + h + 1 := ring

theorem pairCount (n: Nat) (p: Nat) (twice: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [twice]
-- end ring

-- begin ring-coefficients
theorem scaledUp (a: Int) (b: Int) (half: a = 2 * b): 4 * a = 8 * b := ring [4 * half]

theorem bothScaled (x: Int) (y: Int) (k: Int) (sum: x + y = 10) (gap: x - y = 2): 2 * k * x = 12 * k := ring [k * sum, k * gap]

theorem turnedRound (a: Int) (b: Int) (h: a = b + 1): b - a = -1 := ring [-h]
-- end ring-coefficients

-- begin cases
theorem orComm (a: Bool) (b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem andLeft (a: Bool) (b: Bool) (h: (a ∧ b) = True): a = True := cases

def clamp (lo: Nat) (hi: Nat) (x: Nat): Nat := if x < lo then lo else if hi < x then hi else x

theorem clampBelow (lo: Nat) (hi: Nat) (x: Nat) (ordered: lo ≤ hi): clamp lo hi x ≤ hi := cases
-- end cases

-- begin spec
-- The specification: the plain recursive sum.
def sumTo: Nat → Nat
  | 0 => 0
  | Succ k => Succ k + sumTo k

-- The program: a loop with an accumulator.
def sumFast (n: Nat): Nat :=
  def loop: Nat → Nat → Nat
    | 0, total => total
    | Succ k, total => loop k (total + Succ k)
  loop n 0

-- What the loop computes, for any accumulator: the general statement is
-- what makes the induction go through.
theorem loopIsSum (n: Nat) (total: Nat): sumFast.loop n total = total + sumTo n := match n, total with
  | Zero, total => rfl
  | Succ k, total => omega [loopIsSum k (total + Succ k)]

theorem sumFastIsSum (n: Nat): sumFast n = sumTo n := loopIsSum n 0
-- end spec

-- begin induct
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length :=
  match induct (countAbove k xs) with
    | eq1 => omega
    | eq2IfTrue y ys h ih => ih
    | eq2IfFalse y ys h ih => omega

theorem skipsSmall (k: Nat) (x: Nat) (xs: List Nat) (h: (k <= x) = False): countAbove k [x, ..xs] = countAbove k xs :=
  countAbove.eq2.ifFalse k x xs h
-- end induct

-- begin guard-eqs
def cap (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem capKeeps (limit: Nat) (n: Nat) (fits: n ≤ limit): cap limit n = n := cap.eq1 limit n fits

theorem capCuts (limit: Nat) (n: Nat) (over: (n <= limit) = False): cap limit n = limit := cap.eq2 limit n over

def skipThree: Nat → Nat
  | n if n != 3 => n
  | _ => 0

theorem skipThreeKeeps (n: Nat) (other: n ≠ 3): skipThree n = n := skipThree.eq1 n other

theorem skipThreeDrops: skipThree 3 = 0 := skipThree.eq2 3 rfl
-- end guard-eqs

-- begin guard-induct
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost (xs: List Nat): countBig xs ≤ xs.length :=
  match induct (countBig xs) with
    | eq1 => omega
    | eq2 x rest big ih => omega
    | eq3 x rest small ih => omega
-- end guard-induct

-- begin opaque
opaque def checksum (xs: List Nat): Nat := xs.foldLeft 0 (sum x => (sum * 31 + x) % 65521)

theorem checksumNil: checksum [] = 0 unfolding checksum := rfl

test "checksum" := checksum [1, 2] == 33
-- end opaque

-- begin match-equation
def clampTo (limit: Nat) (n: Nat): Nat := if n ≤ limit then n else limit

theorem clampToAtMost (limit: Nat) (n: Nat): clampTo limit n ≤ limit :=
  match fits: Nat.leq n limit with
    | True => fits
    | False => Nat.leRefl limit
-- end match-equation

-- begin match-lemma
theorem clampToFits (limit: Nat) (n: Nat): clampTo limit n ≤ limit ∧ clampTo limit n ≤ n :=
  match fits: Nat.leq n limit with
    | True => Both (clampToAtMost limit n) (Nat.leRefl n)
    | False => Both (clampToAtMost limit n) omega
-- end match-lemma

-- begin decide
def firstOr (fallback: Nat) (xs: List Nat): Nat :=
  if nonempty: 0 < xs.length then xs.headOr fallback else fallback

def safeAt (v: Vec Nat 3) (i: Nat): Option Nat :=
  if inRange: i < 3 then Some (v.getLt i) else None
-- end decide

-- begin bool-statement
def isSmall (n: Nat): Bool := n <= 3

theorem smallBoth (m: Nat) (n: Nat) (h: isSmall m ∧ isSmall n): isSmall n := h.right

theorem smallSame (n: Nat) (h: isSmall n): isSmall n = True := h
-- end bool-statement

-- begin readings
type Within (lo: Nat) (x: Nat) (hi: Nat): Prop = {
  low: lo ≤ x,
  high: x ≤ hi
}

def within (lo: Nat) (x: Nat) (hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem withinReads (lo: Nat) (x: Nat) (hi: Nat): within lo x hi ↔ Within lo x hi := {
  forward = h => { low = h.left, high = h.right },
  backward = r => Both r.low r.high
}

theorem withinHigh (lo: Nat) (x: Nat) (hi: Nat) (h: within lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem withinLow (lo: Nat) (x: Nat) (hi: Nat) (h: within lo x hi): lo ≤ x := h.read.low

theorem withinSelf (x: Nat): within x x x := { low = Nat.leRefl x, high = Nat.leRefl x }

theorem eitherSide (a: Bool) (b: Bool) (h: (a || b) = True): b ∨ a :=
  match h with
    | Inl ha => Inr ha
    | Inr hb => Inl hb
-- end readings

-- begin readings-decisions
theorem sameKey [auto eq: DecEq k] (a b c: k) (h: (a == b && b == c) = True): a = c :=
  match h with
    | Both ab bc => rewrite ab.read, bc.read in rfl

theorem differ [auto eq: DecEq k] (a b: k) (h: (a == b) = False): a ≠ b := h.read
-- end readings-decisions

-- begin readings-auto
def small (x: Nat) [auto ok: x < 5]: Nat := x

def member (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: xs.all (x => x < 5) = True): Nat := small y

theorem inRight (x: Nat) (xs: List Nat) (b: Bool) (h: (b && xs.contains x) = True): x ∈ xs := cases
-- end readings-auto

-- begin dependent
def pick (v: Vec Nat 3): Nat := v.get 2

theorem pickTrio: pick (VCons 1 (VCons 2 (VCons 3 VNil))) = 3 := rfl
-- end dependent

-- begin reify
theorem orElseIsGetOrElse (fallback: a) (t: () → {Fail} a): Fail.orElse fallback t = (Fail.toOption t).getOrElse fallback :=
  match reify t with
    | return x => rfl
    | Fail.stop message, _ => rfl
-- end reify

-- begin funext
theorem doubleIsTimesTwo: double = (n => 2 * n) := Quot.funext Nat (n => Nat) double (n => 2 * n) twiceIsDouble
-- end funext

-- begin export
export def clampPercent (n: Nat): Nat := clampTo 100 n

theorem clampPercentAtMost (n: Nat): clampPercent n ≤ 100 := clampToAtMost 100 n
-- end export

test "the program agrees with the specification on an example" := sumFast 100 == 5050 ∧ sumTo 100 == 5050

-- begin logic
theorem headIn (x: Nat) (rest: List Nat): x ∈ [x, ..rest] := Inl rfl

theorem notInEmpty (x: Nat): x ∉ [] := none => none

theorem bothWays (p: Prop) (q: Prop): p ∧ q ↔ q ∧ p := {
  forward = h => Both (And.right h) (And.left h),
  backward = h => Both (And.right h) (And.left h)
}

theorem hasSquareRoot: ∃ (n: Nat) => n * n = 49 := Witness 7 rfl

def unseen (seen: List Nat) (xs: List Nat): List Nat := xs.filter (x => x ∉ seen)
-- end logic

-- begin forall
theorem zeroPlusAll: ∀ (n: Nat) => 0 + n = n := n => rfl

theorem atOneAndTwo (p: Nat -> Prop) (all: ∀ (n: Nat) => p n): p 1 ∧ p 2 := Both (all 1) (all 2)

theorem swapSum (comm: ∀ (a b: Nat) => a + b = b + a): 2 + 5 = 5 + 2 := comm 2 5
-- end forall

test "unseen" := unseen [1, 2] [1, 2, 3] == [3]
