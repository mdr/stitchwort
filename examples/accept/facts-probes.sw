-- `byFacts` closes each goal that `cases` failed on in SW-4483's probes
-- (docs/reviews/SW-4483/cases-probes.txt), with the other probes beside
-- them: a part of an `∧` fact, an implication between plain propositions,
-- chained implications, a local `∀` fact applied once or with an unknown
-- only a fact fixes, an `∃` fact, and an equation in scope.

theorem computedParts ∀ (n: Nat) (h: 3 ≤ n): (1 ≤ 2) ∧ ((2 == 2) = True) ∧ (2 < n + 5) := byFacts

theorem localForallTwo ∀ (p q: Nat → Bool) (g: Nat → Prop) (step: ∀ (x: Nat) => p x = True → q x = True → g x)
    (a: p 3 = True)
    (b: q 3 = True):
    g 3 :=
  byFacts

theorem localForall ∀ (p: Nat → Bool) (g: Nat → Prop) (step: ∀ (x: Nat) => p x = True → g x) (a: p 3 = True): g 3 :=
  byFacts

theorem twoPremises ∀ (a b c: Prop) (f: a → b → c) (x: a) (y: b): c := byFacts

theorem testPart ∀ (a b c: Bool) (h: (a && b && c) = True): b = True := byFacts

theorem existsPart ∀ (p q: Nat → Bool) (h: ∃ (n: Nat) => p n = True ∧ q n = True): ∃ (n: Nat) => q n = True := byFacts

theorem chained ∀ (a b c d: Prop) (f: a → b) (g: b → c) (k: c → d) (x: a): d := byFacts

theorem equationNat ∀ (f: Nat → Nat) (a b: Nat) (e: a = b) (h: f b = 0): f a = 0 := byFacts

theorem equationList ∀ (xs ys: List Nat) (f: List Nat → Nat) (e: xs = ys) (h: f ys = 0): f xs = 0 := byFacts

theorem applyToPart ∀ (a b c: Prop) (h: a ∧ b) (f: a → c): c ∧ b := byFacts

theorem implication ∀ (a b: Prop) (f: a → b) (x: a): b := byFacts

theorem testImplication ∀ (p q: Bool) (f: p = True → q = True) (x: p = True): q = True := byFacts

theorem unknownFromFact ∀ (p q r: Nat → Prop) (step: ∀ (x y: Nat) => p x → q y → r y) (hp: p 5) (hq: q 3): r 3 :=
  byFacts
