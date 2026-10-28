-- Chapter 10: proofs.
import Std (Eq, Exists, Fail, Fin, Iff, List, Nat, Option, Quot, Vec)
import Std.Exists (Witness)

-- begin rfl
def double (n: Nat): Nat := n + n

theorem doubleFour: double 4 = 8 := rfl

theorem zeroPlus (n: Nat): 0 + n = n := rfl
-- end rfl

-- begin induction
theorem plusZero: (n: Nat) → n + 0 = n
  | Zero => rfl
  | Succ k => Eq.cong Succ (plusZero k)
-- end induction

-- begin lists
def mapList (f: a → b): List a → List b
  | [] => []
  | Cons x rest => Cons (f x) (mapList f rest)

theorem lengthMapList (f: a → b): (xs: List a) → (mapList f xs).length = xs.length
  | [] => rfl
  | Cons x rest => Eq.cong Succ (lengthMapList f rest)
-- end lists

-- begin rewrite
theorem swapWithZero (a: Nat) (b: Nat): a + b + 0 = b + a :=
  rewrite Nat.addZero (a + b), Nat.addComm a b
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
-- end omega

-- begin omega-logic
def isNeighbour (a: Nat) (b: Nat): Bool := a + 1 == b || b + 1 == a

theorem neighboursDiffer (a: Nat) (b: Nat) (near: isNeighbour a b = True): a != b := omega

theorem nearZero (a: Nat) (h: a ≤ 1): Or (a = 0) (a = 1) := omega
-- end omega-logic

-- begin ring
theorem squareOfSum (a: Nat) (b: Nat): (a + b) * (a + b) = a * a + 2 * a * b + b * b := ring

theorem areaGrows (w: Nat) (h: Nat): (w + 1) * (h + 1) = w * h + w + h + 1 := ring

theorem pairCount (n: Nat) (p: Nat) (twice: p + p + n = n * n): (n + p) + (n + p) + Succ n = Succ n * Succ n := ring [twice]
-- end ring

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
theorem loopIsSum: (n: Nat) → (total: Nat) → sumFast.loop n total = total + sumTo n
  | Zero, total => Eq.sym (Nat.addZero total)
  | Succ k, total => omega [loopIsSum k (total + Succ k)]

theorem sumFastIsSum (n: Nat): sumFast n = sumTo n := loopIsSum n 0
-- end spec

-- begin match-equation
def clampTo (limit: Nat) (n: Nat): Nat := if n ≤ limit then n else limit

theorem clampToAtMost (limit: Nat) (n: Nat): clampTo limit n ≤ limit :=
  match fits: Nat.leq n limit with
    | True => fits
    | False => Nat.leRefl limit
-- end match-equation

-- begin decide
def firstOr (fallback: Nat) (xs: List Nat): Nat :=
  if nonempty: 0 < xs.length then xs.headOr fallback else fallback

def safeAt (v: Vec Nat 3) (i: Nat): Option Nat :=
  if inRange: i < 3 then Some (v.getLt i) else None
-- end decide

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
theorem headIn (x: Nat) (rest: List Nat): x ∈ Cons x rest := Inl rfl

theorem notInEmpty (x: Nat): x ∉ Nil := none => none

theorem bothWays (p: Prop) (q: Prop): p ∧ q ↔ q ∧ p := {
  forward = h => Both (And.right h) (And.left h),
  backward = h => Both (And.right h) (And.left h)
}

theorem hasSquareRoot: ∃ (n: Nat) => n * n = 49 := Witness 7 rfl

def unseen (seen: List Nat) (xs: List Nat): List Nat := xs.filter (x => x ∉ seen)
-- end logic

test "unseen" := unseen [1, 2] [1, 2, 3] == [3]
