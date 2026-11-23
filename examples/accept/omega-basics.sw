-- `arithmetic` proves linear arithmetic over `Nat`: it reads the hypotheses and the
-- goal, searches for a certificate and writes the proof itself. Each theorem
-- below shows one case.

import Std (Nat, Bool, Void, List)

-- Nat domain: every atom is at least zero, so no hypotheses are needed.
theorem leAddRight ∀ (x y: Nat): x ≤ x + y := arithmetic

-- Multiplication by a literal is repeated addition, whichever side the literal is on.
theorem mulRight3 ∀ (x: Nat): x * 3 = x + x + x := arithmetic

theorem mulLeft3 ∀ (x: Nat): 3 * x = x + x + x := arithmetic

theorem mulRight3b ∀ (x: Nat): x + x + x = x * 3 := arithmetic

theorem mulLeft3b ∀ (x: Nat): x + x + x = 3 * x := arithmetic

theorem mul0 ∀ (x: Nat): x * 0 = 0 := arithmetic

theorem mul0b ∀ (x: Nat): 0 * x = 0 := arithmetic

theorem mul1 ∀ (x: Nat): x * 1 = x := arithmetic

theorem mul1b ∀ (x: Nat): 1 * x = x := arithmetic

-- Association is kept as written, and the proof still goes through.
theorem assoc ∀ (a b c: Nat): (a + b) + c ≤ a + (b + c) := arithmetic

-- Boolean preprocessing: hypotheses written with `Nat.leq`, `&&`, `Not`, `And`
-- or `=` are read as facts.
theorem leqFalseHyp ∀ (a b: Nat) (h: Nat.leq a b = False): b < a := arithmetic

theorem andHyp ∀ (a b c: Nat) (h: (a ≤ b ∧ b ≤ c) = True): a ≤ c := arithmetic

-- The Day 5 arm: a range holds `id`, and the next range starts after the end.
theorem absorbTrue ∀ (lastFrom id lastTo rFrom: Nat)
    (i: (lastFrom ≤ id ∧ id ≤ lastTo) = True)
    (e: Nat.leq rFrom (lastTo + 1) = False):
    id < rFrom :=
  arithmetic

theorem notLe ∀ (a b: Nat) (h: ¬(a ≤ b)): b < a := arithmetic

theorem notLt ∀ (a b: Nat) (h: ¬(a < b)): b ≤ a := arithmetic

theorem propAnd ∀ (a b c: Nat) (h: (a ≤ b) ∧ (b ≤ c)): a ≤ c := arithmetic

-- Equations are facts too.
theorem eqHyp ∀ (a b c: Nat) (h1: a = b + 1) (h2: b = c + 1): a = c + 2 := arithmetic

-- Goal forms: `<`, `<=`, `=`, a closed goal, `Not`, `Nat.leq`, `And` and `&&`.
theorem ltGoal ∀ (a: Nat): a < a + 1 := arithmetic

theorem leGoal ∀ (a b: Nat) (h: a < b): a ≤ b := arithmetic

theorem antisym ∀ (a b: Nat) (h1: a ≤ b) (h2: b ≤ a): a = b := arithmetic

theorem closedGoal: 2 < 3 := arithmetic

theorem notGoal ∀ (x y: Nat) (h: x < y): ¬(y ≤ x) := arithmetic

theorem leqFalseGoal ∀ (x y: Nat) (h: x < y): Nat.leq y x = False := arithmetic

theorem andGoal ∀ (a b: Nat) (h: a < b): (a ≤ b) ∧ (a + 1 ≤ b) := arithmetic

theorem boolAndGoal ∀ (a b: Nat) (h: a < b): (a ≤ b ∧ a + 1 ≤ b) = True := arithmetic

-- Contradictions: the goal is `Void`, or the facts alone can't hold.
theorem threeLtTwo ∀ (h: 3 < 2): Void := arithmetic

-- The facts contradict each other, so any goal follows, even one about other atoms.
theorem disconnected ∀ (x y: Nat) (h: y < y): x < 0 := arithmetic

theorem void2 ∀ (x y: Nat) (h1: x + 1 ≤ y) (h2: y ≤ x): Void := arithmetic

-- Integer reasoning: `2 * x` is never `1`, found by dividing the row by 2.
theorem twoXEqOne ∀ (x: Nat) (h: 2 * x = 1): Void := arithmetic

-- Four constraints with no integer solution, found by splitting a case.
theorem splitRegression ∀ (x y: Nat)
    (h1: 1 ≤ 2 * x + 3 * y)
    (h2: 2 * x + 3 * y ≤ 4)
    (h3: 2 * y ≤ 3 * x + 1)
    (h4: 3 * x ≤ 2 * y + 2):
    Void :=
  arithmetic

-- Extra facts: `arithmetic [...]` adds proofs to the hypotheses, here an instance of a general fact.
theorem viaList ∀ (a b: Nat) (f: Nat → Nat) (h: ∀ (n: Nat) => n ≤ f n): a ≤ f a + b := arithmetic [h a]

-- `arithmetic` as the proof of a `calc` step.
theorem calcStep ∀ (a b: Nat) (h: a + 2 ≤ b): a < b := calc a
  _ < a + 1 := arithmetic
  _ ≤ b := arithmetic

-- `arithmetic` inside a local theorem.
theorem localDef ∀ (a b: Nat): a ≤ a + b :=
  theorem helper: 0 ≤ b := arithmetic
  arithmetic

-- An `arithmetic` equation consumed by `rewrite`, in both directions.
theorem viaRewrite ∀ (x: Nat) (f: Nat → Nat) (h: f (x + x + x) = 7): f (x * 3) = 7 :=
  rewrite (arithmetic: x * 3 = x + x + x) then h

theorem castBy ∀ (x: Nat) (h: x * 3 = 21): x + x + x = 21 := rewrite <- (arithmetic: x * 3 = x + x + x) then h

-- Cost: `k * x` unfolds `k` times when its type is checked, so `arithmetic` takes
-- `k` up to 1000 (omega-mul-left-limit.sw); `x * k` stays as written, at any size.
theorem big0 ∀ (x: Nat) (h: 10 * x ≤ 20): x ≤ 2 := arithmetic

theorem big1 ∀ (x: Nat) (h: 1000 * x ≤ 2000): x ≤ 2 := arithmetic

theorem bigR0 ∀ (x: Nat) (h: x * 10 ≤ 20): x ≤ 2 := arithmetic

theorem bigR ∀ (x: Nat) (h: x * 1000000 ≤ 2000000): x ≤ 2 := arithmetic

-- A subexpression mentioned many times is one atom, however often it appears.
theorem shared ∀ (xs ys: List Nat)
    (h1: List.length (List.append xs ys) + xs.length ≤ 20)
    (h2: 3 ≤ List.length (List.append xs ys))
    (h3: List.length (List.append xs ys) ≤ xs.length + 10)
    (h4: xs.length + List.length (List.append xs ys) ≤ 18):
    xs.length ≤ 17 :=
  arithmetic

-- Proof-dependent atoms: the same call with the same proof is the same atom.
def getP: (n: Nat) → n < 10 → Nat
  | Zero, h => 0
  | Succ k, h => k

theorem sameProof ∀ (n: Nat) (h1: n < 10): getP n h1 ≤ getP n h1 := arithmetic
