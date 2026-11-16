-- Tuples build and take apart proofs of `∃` and `∧`
-- (docs/proposals/proof-tuples.md, D3631): read against the type they meet,
-- `(x, a, b)` is `Witness x (Both a b)`, nesting to the right as the chain
-- `∃ x => A ∧ B` does. On data a tuple is still a pair.

import Std (byDecision)

-- Building, where the goal is known.
theorem small: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, byComputing)

-- With nothing expected, a tuple whose first part is a proof proves `∧`.
theorem swapped ∀ (p q: Prop) (a: p) (b: q): q ∧ p :=
  let both := (b, a)
  both

-- A definition that unfolds to a chain takes a tuple as its constructors.
def Square (m: Nat): Prop := ∃ (n: Nat) => n * n = m ∧ n > 0

theorem fortyNine: Square 49 := (7, byComputing, byDecision)

-- Taking apart: in a `match` arm.
theorem rootOf ∀ (h: ∃ (n: Nat) => n > 2 ∧ n * n = 49): ∃ (m: Nat) => m * m = 49 := match h with
  | (n, _, square) => (n, square)

-- In a `let`, which in a proof is the one-arm `match`.
theorem rootOfLet ∀ (h: ∃ (n: Nat) => n > 2 ∧ n * n = 49): ∃ (m: Nat) => m * m = 49 :=
  let (n, _, square) := h
  (n, square)

-- The last part may stand for the rest of the chain.
theorem rest ∀ (p q r: Prop) (h: p ∧ q ∧ r): q ∧ r :=
  let (_, more) := h
  more

-- A part that is itself a chain on the left nests visibly.
theorem leftNested ∀ (p q r: Prop) (h: (p ∧ q) ∧ r): r ∧ p :=
  let ((a, _), c) := h
  (c, a)

-- A goal that is a proposition variable: still the `match`, as `∃` has no
-- projections.
theorem varGoal ∀ (pred: Nat → Prop) (q: Prop) (h: ∃ (n: Nat) => pred n ∧ q): q :=
  let (_, _, b) := h
  b

-- A lambda's parameter, and a clause lambda.
theorem viaLambda ∀ (p q: Prop) (use: (p ∧ q → q) → q): q := use ((_, b) => b)

theorem viaClause ∀ (p q: Prop) (use: (p ∧ q → q) → q): q := use (match | (_, b) => b)

-- A definition by arms.
theorem byArms ∀ (p q: Prop): p ∧ q → Nat → q ∧ p
  | (a, b), _ => (b, a)

-- Data in a tuple is still a pair, beside a proof tuple.
def withProof (n: Nat): (Nat, Nat) := (n, n + 1)

theorem pairStill: withProof 1 = (1, 2) := byComputing

-- `.left` and `.right` project a proof of `∧`.
theorem projected ∀ (p q: Prop) (h: p ∧ q): q := h.right
