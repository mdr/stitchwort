-- `byFacts [lemmas]` (docs/syntax.md, "byFacts"): a named lemma whose
-- unknown only a fact fixes, an `∃` goal whose witness a fact fixes, a
-- record of proofs as a goal and as a fact, a local `∀` applied twice, and
-- an equation between constructors in scope.

theorem lessTrans ∀ (a b c: Nat) (ab: a < b) (bc: b < c): a < c := arithmetic

-- `b` is in neither the goal nor the call: `h.left` fixes it as `y`.
theorem viaMiddle ∀ (x y z: Nat) (h: x < y ∧ y < z): x < z := byFacts [lessTrans]

-- The witness is `n`, from the fact `q n`, never a guess.
theorem existsSwap ∀ (p q: Nat → Prop) (h: ∃ (n: Nat) => p n ∧ q n): ∃ (n: Nat) => q n ∧ p n := byFacts

type Within (low: Nat) (high: Nat) (n: Nat): Prop = {
  above: low ≤ n,
  below: n < high
}

-- A record of proofs as the goal: each field a part.
theorem withinOf ∀ (n: Nat) (h: (2 ≤ n) ∧ (n < 9)): Within 2 9 n := byFacts

-- And as a fact: its fields are facts.
theorem withinParts ∀ (n: Nat) (w: Within 2 9 n): (n < 9) ∧ (2 ≤ n) := byFacts

-- A test fact read as its parts, closing a record.
theorem withinTest ∀ (n: Nat) (h: (2 ≤ n && n < 9) = True): Within 2 9 n := byFacts

-- A local `∀` applied twice: `step 1 (step 0 base)`.
theorem stepTwice ∀ (p: Nat → Prop) (step: ∀ (x: Nat) => p x → p (x + 1)) (base: p 0): p 2 := byFacts

-- An equation between constructors gives its fields' equation, whose
-- variable side is then replaced.
theorem someEqual ∀ (f: Nat → Nat) (x y: Nat) (e: Some x = Some y) (h: f x = 0): f y = 0 := byFacts
