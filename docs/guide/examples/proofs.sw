-- Chapter 10: proofs.
import Std (Eq, Exists, Fail, Fin, Iff, Int, List, Nat, Option, Parse, Quot, Vec, byDecision)
import Std.Exists (Witness)

-- begin byComputing
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := byComputing

theorem zeroPlus ∀ (n: Nat): 0 + n = n := byComputing
-- end byComputing

-- begin induction
theorem timesOne ∀ (n: Nat): n * 1 = n := match n with
  | Zero => byComputing
  | Succ k => Eq.cong Succ (timesOne k)
-- end induction

-- begin lists
def mapList (f: a → b): List a → List b
  | [] => []
  | [x, ..rest] => [f x, ..mapList f rest]

theorem lengthMapList ∀ (f: a → b) (xs: List a): (mapList f xs).length = xs.length := match xs with
  | [] => byComputing
  | [x, ..rest] => Eq.cong Succ (lengthMapList f rest)
-- end lists

-- begin rewrite
theorem swapTimesOne ∀ (a b: Nat): (a + b) * 1 = b + a := rewrite Nat.mulOne (a + b), Nat.addComm a b
-- end rewrite

-- begin rewrite-repeatedly
theorem regroup ∀ (xs ys zs: List Nat): ((xs ++ ys) ++ zs) ++ [] = xs ++ (ys ++ zs) :=
  rewrite repeatedly [List.appendAssoc, List.appendNil]

theorem joined ∀ (xs ys: List Nat) (h: xs ++ ys = ys): (xs ++ []) ++ ys = ys := rewrite repeatedly [List.appendNil]
-- end rewrite-repeatedly

-- begin rule-sets
rules appends := [List.appendAssoc, List.appendNil]

theorem regroupFrom ∀ (xs ys zs: List Nat) (h: ys = zs): (xs ++ ys) ++ [] = xs ++ zs := rewrite repeatedly [h, appends]

theorem fromFact ∀ (xs ys: List Nat) (h: (xs ++ ys) ++ [] = [1]): xs ++ ys = [1] :=
  rewrite repeatedly [appends] at h then h
-- end rule-sets

-- begin calc
theorem chain ∀ (a b c: Nat) (ab: a = b) (bc: b ≤ c) (small: c < 10): a < 10 := calc a
  _ = b := ab
  _ ≤ c := bc
  _ < 10 := small
-- end calc

-- begin stated
theorem swappedSum ∀ (a b c: Nat): (a + b) * 1 + c = b + a + c :=
  let swapped: (a + b) * 1 = b + a := rewrite Nat.mulOne (a + b), Nat.addComm a b
  rewrite swapped
-- end stated

-- begin arithmetic
theorem roomForOne ∀ (x y: Nat) (before: x < y) (limit: y ≤ 10): x + 1 ≤ 10 := arithmetic

theorem twiceIsDouble ∀ (n: Nat): double n = 2 * n := arithmetic

theorem stepBack ∀ (n: Nat) (x: Int) (h: x < n.toInt): x - 1 < n.toInt - 1 := arithmetic

theorem thirdOfTriple ∀ (k: Int): (3 * k) / 3 = k := arithmetic

theorem sizeOfSum ∀ (x y: Int): (x + y).natAbs ≤ x.natAbs + y.natAbs := arithmetic
-- end arithmetic

-- begin omega-logic
def isNeighbour (a b: Nat): Bool := a + 1 == b || b + 1 == a

theorem neighboursDiffer ∀ (a b: Nat) (near: isNeighbour a b = True): a != b := arithmetic

theorem nearZero ∀ (a: Nat) (h: a ≤ 1): a = 0 ∨ a = 1 := arithmetic
-- end omega-logic

-- begin ring
theorem squareOfSum ∀ (a b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := algebra

theorem areaGrows ∀ (w h: Nat): (w + 1) * (h + 1) = w * h + w + h + 1 := algebra

theorem pairCount ∀ (n p: Nat) (twice: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n :=
  algebra [twice]
-- end ring

-- begin ring-coefficients
theorem scaledUp ∀ (a b: Int) (half: a = 2 * b): 4 * a = 8 * b := algebra [4 * half]

theorem bothScaled ∀ (x y k: Int) (sum: x + y = 10) (gap: x - y = 2): 2 * k * x = 12 * k := algebra [k * sum, k * gap]

theorem turnedRound ∀ (a b: Int) (h: a = b + 1): b - a = -1 := algebra [-h]
-- end ring-coefficients

-- begin cases
theorem orComm ∀ (a b: Bool): (a ∨ b) = (b ∨ a) := cases

theorem andLeft ∀ (a b: Bool) (h: (a ∧ b) = True): a = True := cases

def clamp (lo hi x: Nat): Nat :=
  if x < lo then lo
  else if hi < x then hi
  else x

theorem clampBelow ∀ (lo hi x: Nat) (ordered: lo ≤ hi): clamp lo hi x ≤ hi := cases
-- end cases

-- begin cases-constructors
theorem someSame ∀ (f: Nat → Nat) (x y: Nat) (h: Some x = Some y): f x = f y := cases
-- end cases-constructors

-- begin cases-once
def total: List Nat → Nat
  | [] => 0
  | [x, ..rest] => x + total rest

def dropLeadingZero: List Nat → List Nat
  | [0, ..rest] => rest
  | other => other

theorem dropKeepsTotal ∀ (xs: List Nat): total (dropLeadingZero xs) = total xs := cases

def isSpace: Char → Bool
  | ' ' => True
  | '\t' => True
  | _ => False

theorem spaceIsSmall ∀ (c: Char) (space: isSpace c = True): c.toNat ≤ 32 := cases
-- end cases-once

-- begin cases-named
def bonus (lit: Bool) (n: Nat): Nat := if lit then n + 2 else n + 1

theorem bonusGrows ∀ (lit: Bool) (n: Nat): n < bonus lit n := cases lit then arithmetic

theorem smallSum ∀ (n: Nat) (h: n = 1 ∨ n = 2 ∨ n = 4): n + n ≤ 8 := cases h then arithmetic
-- end cases-named

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
theorem loopIsSum ∀ (n total: Nat): sumFast.loop n total = total + sumTo n := match n, total with
  | Zero, total => byComputing
  | Succ k, total => arithmetic [loopIsSum k (total + Succ k)]

theorem sumFastIsSum ∀ (n: Nat): sumFast n = sumTo n := loopIsSum n 0
-- end spec

-- begin induct
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length := match induct (countAbove k xs) with
  | eq1 => arithmetic
  | eq2IfTrue y ys h ih => ih
  | eq2IfFalse y ys h ih => arithmetic

theorem skipsSmall ∀ (k x: Nat) (xs: List Nat) (h: (k <= x) = False): countAbove k [x, ..xs] = countAbove k xs :=
  countAbove.eq2.ifFalse k x xs h
-- end induct

-- begin induct-cases
theorem countAboveLeShared ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length := match induct (countAbove k xs) with
  | eq1 => arithmetic
  | eq2IfTrue y ys h ih | eq2IfFalse y ys h ih => arithmetic

type Pile = | Empty | More (weight: Nat) (rest: Pile)

def Pile.total: Pile → Nat
  | Empty => 0
  | More weight rest => weight + Pile.total rest

theorem totalAtLeastZero ∀ (pile: Pile): pile.total ≥ 0 := match induct pile.total with
  | eq1 => arithmetic
  | eq2 weight rest ih => arithmetic
-- end induct-cases

-- begin guard-eqs
def cap (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem capKeeps ∀ (limit n: Nat) (fits: n ≤ limit): cap limit n = n := cap.eq1 limit n fits

theorem capCuts ∀ (limit n: Nat) (over: (n <= limit) = False): cap limit n = limit := cap.eq2 limit n over

def skipThree: Nat → Nat
  | n if n != 3 => n
  | _ => 0

theorem skipThreeKeeps ∀ (n: Nat) (other: n ≠ 3): skipThree n = n := skipThree.eq1 n other

theorem skipThreeDrops: skipThree 3 = 0 := skipThree.eq2 3 byComputing
-- end guard-eqs

-- begin cases-guards
type TokenStart = | WordStart | DigitsStart | OtherStart

def tokenStart: List Char → Option TokenStart
  | [' ', .._] => None
  | [c, .._] if c.isAsciiLetter => Some WordStart
  | [c, .._] if c.isAsciiDigit => Some DigitsStart
  | [_, .._] => Some OtherStart
  | [] => None

theorem wordStartLetter ∀ (c: Char) (rest: List Char)
    (starts: tokenStart [c, ..rest] = Some WordStart):
    c.isAsciiLetter = True :=
  cases
-- end cases-guards

-- begin guard-refines
theorem capAtMost ∀ (limit n: Nat): cap limit n <= limit := match n with
  | n if n <= limit => arithmetic
  | _ => arithmetic
-- end guard-refines

-- begin guard-induct
def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost ∀ (xs: List Nat): countBig xs ≤ xs.length := match induct (countBig xs) with
  | eq1 => arithmetic
  | eq2 x rest big ih => arithmetic
  | eq3 x rest small ih => arithmetic
-- end guard-induct

-- begin opaque
opaque def checksum (xs: List Nat): Nat := xs.foldLeft 0 (sum x => (sum * 31 + x) % 65521)

theorem checksumNil: checksum [] = 0 unfolding checksum := byComputing

test "checksum" := checksum [1, 2] == 33
-- end opaque

-- begin match-equation
def clampTo (limit n: Nat): Nat := if n ≤ limit then n else limit

theorem clampToAtMost ∀ (limit n: Nat): clampTo limit n ≤ limit := match fits: Nat.leq n limit with
  | True => fits
  | False => Nat.leRefl limit
-- end match-equation

-- begin match-lemma
theorem clampToFits ∀ (limit n: Nat): clampTo limit n ≤ limit ∧ clampTo limit n ≤ n := match fits: Nat.leq n limit with
  | True => Both (clampToAtMost limit n) (Nat.leRefl n)
  | False => Both (clampToAtMost limit n) arithmetic
-- end match-lemma

-- begin match-uncovered
def spare (n: Nat): Bool := 10 < n
def drop (n: Nat): Option Nat := if spare n then None else Some n
def kept (x: Option Nat): Bool := match x with
  | Some n => not (spare n)
  | None => True

theorem keptAfter ∀ (n: Nat): kept (drop n) = True := match spare n with
  | True => byComputing
  | False => byComputing
-- end match-uncovered

-- begin decide
def firstOr (fallback: Nat) (xs: List Nat): Nat := if nonempty: 0 < xs.length then xs.headOr fallback else fallback

def safeAt (v: Vec Nat 3) (i: Nat): Option Nat := if inRange: i < 3 then Some (v.getLt i) else None
-- end decide

-- begin bool-statement
def isSmall (n: Nat): Bool := n <= 3

theorem smallBoth ∀ (m n: Nat) (h: isSmall m ∧ isSmall n): isSmall n := h.right

theorem smallSame ∀ (n: Nat) (h: isSmall n): isSmall n = True := h
-- end bool-statement

-- begin readings
type Within (lo: Nat) (x: Nat) (hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }

def within (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem withinReads ∀ (lo x hi: Nat): within lo x hi ↔ Within lo x hi :=
  { forward = h => { low = h.left, high = h.right }, backward = r => Both r.low r.high }

theorem withinHigh ∀ (lo x hi: Nat) (h: within lo x hi): x ≤ hi := match h with | { low, high } => high

theorem withinLow ∀ (lo x hi: Nat) (h: within lo x hi): lo ≤ x := h.read.low

theorem withinSelf ∀ (x: Nat): within x x x := { low = Nat.leRefl x, high = Nat.leRefl x }

theorem eitherSide ∀ (a b: Bool) (h: (a || b) = True): b ∨ a := match h with
  | Inl ha => Inr ha
  | Inr hb => Inl hb
-- end readings

-- begin readings-decisions
theorem sameKey ∀ [auto eq: DecEq k] (a b c: k) (h: (a == b && b == c) = True): a = c := match h with
  | Both ab bc => rewrite ab.read, bc.read

theorem differ ∀ [auto eq: DecEq k] (a b: k) (h: (a == b) = False): a ≠ b := h.read
-- end readings-decisions

-- begin readings-auto
def small (x: Nat) [auto ok: x < 5]: Nat := x

def member (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: xs.all (x => x < 5) = True): Nat := small y

theorem inRight ∀ (x: Nat) (xs: List Nat) (b: Bool) (h: (b && xs.contains x) = True): x ∈ xs := cases
-- end readings-auto

-- begin dependent
def pick (v: Vec Nat 3): Nat := v.get 2

theorem pickTrio: pick (VCons 1 (VCons 2 (VCons 3 VNil))) = 3 := byComputing
-- end dependent

-- begin reify
theorem orElseIsGetOrElse ∀ (fallback: a) (t: () → {Fail} a):
    Fail.orElse fallback t = (Fail.toOption t).getOrElse fallback :=
  match reify t with
    | return x => byComputing
    | Fail.stop message, _ => byComputing
-- end reify

-- begin walk
def nextNumber(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesNextNumber: Parse.Gives Parse.Invariant.any (() => nextNumber()) ((seen: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def capped (limit: Nat): {Parse Nat} Nat := match nextNumber() with
  | Some n => if n <= limit then n else limit
  | None => 0

theorem givesCapped ∀ (limit: Nat): Parse.Gives Parse.Invariant.any (() => capped limit) (n => n <= limit) :=
  byWalking []
-- end walk

-- begin funext
theorem doubleIsTimesTwo: double = (n => 2 * n) := Quot.funext Nat (n => Nat) double (n => 2 * n) twiceIsDouble
-- end funext

-- begin export
export def clampPercent (n: Nat): Nat := clampTo 100 n

theorem clampPercentAtMost ∀ (n: Nat): clampPercent n ≤ 100 := clampToAtMost 100 n
-- end export

test "the program agrees with the specification on an example" := sumFast 100 == 5050 ∧ sumTo 100 == 5050

-- begin logic
theorem headIn ∀ (x: Nat) (rest: List Nat): x ∈ [x, ..rest] := Inl byComputing

theorem notInEmpty ∀ (x: Nat): x ∉ [] := none => none

theorem bothWays ∀ (p q: Prop): p ∧ q ↔ q ∧ p :=
  { forward = h => Both h.right h.left, backward = h => Both h.right h.left }

theorem hasSquareRoot: ∃ (n: Nat) => n * n = 49 := Witness 7 byComputing

def unseen (seen xs: List Nat): List Nat := xs.filter (x => x ∉ seen)
-- end logic

-- begin tuples
theorem squareRoot: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, byComputing)

theorem rootOf ∀ (h: ∃ (n: Nat) => n > 2 ∧ n * n = 49): ∃ (m: Nat) => m * m = 49 :=
  let (n, _, square) := h
  (n, square)

theorem swapAnd ∀ (p q: Prop): p ∧ q → q ∧ p
  | (a, b) => (b, a)

theorem secondOf ∀ (p q: Prop) (h: p ∧ q): q := h.right
-- end tuples

-- begin forall
theorem zeroPlusAll ∀ (n: Nat): 0 + n = n := byComputing

theorem atOneAndTwo ∀ (p: Nat -> Prop) (all: ∀ (n: Nat) => p n): p 1 ∧ p 2 := Both (all 1) (all 2)

theorem swapSum ∀ (comm: ∀ (a b: Nat) => a + b = b + a): 2 + 5 = 5 + 2 := comm 2 5
-- end forall

test "unseen" := unseen [1, 2] [1, 2, 3] == [3]

-- begin literal-arms
type Keyword = | Def | Theorem

def keyword (word: Text): Option Keyword := match word with
  | "def" => Some Def
  | "theorem" => Some Theorem
  | _ => None

theorem keywordOther ∀ (word: Text) (notDef: word ≠ "def") (notTheorem: word ≠ "theorem"): keyword word = None :=
  keyword.eq3 word notDef notTheorem

theorem onlyDef ∀ (word: Text) (h: keyword word = Some Def): word = "def" :=
  if isDef: word = "def" then isDef
  else if isTheorem: word = "theorem" then (rewrite isTheorem at h then match Option.someInjective h with | ())
  else (rewrite keywordOther word isDef isTheorem at h then match h with | ())
-- end literal-arms

-- begin catch-all-facts
theorem otherWord ∀ (word: Text): keyword word = None ∨ word = "def" ∨ word = "theorem" := match word with
  | "def" => Inr (Inl byComputing)
  | "theorem" => Inr (Inr byComputing)
  | other => Inl (keyword.eq3 other byDecision byDecision)
-- end catch-all-facts

-- begin or-pattern-proof
theorem keywordLength ∀ (word: Text) (known: word = "def" ∨ word = "let"): word.length = 3 := match known with
  | Inl same | Inr same => rewrite same
-- end or-pattern-proof
