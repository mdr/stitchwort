-- expect-error: E-FACTS
-- The listed lemma's conclusion fits, but its premise `x < y` is in no fact,
-- so its unknown `b` is never fixed: nothing is guessed.

theorem lessTrans ∀ (a b c: Nat) (ab: a < b) (bc: b < c): a < c := arithmetic

theorem noMiddle ∀ (g: Nat → Prop) (x z: Nat) (hz: g z): x * x < z * z := byFacts [lessTrans]
