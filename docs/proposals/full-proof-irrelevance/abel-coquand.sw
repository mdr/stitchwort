-- Probe for docs/proposals/full-proof-irrelevance.md: Abel and Coquand's term
-- (proof-irrelevance.md section 5.2). Under the hypothesis `h` that every two
-- propositions are equal, `bigOmega h` would compute to itself for ever if a
-- cast along any proof of `Top = Top` computed. Every term here is a proof
-- (of `Bot` or `Top`), so a checker that never computes inside a proof never
-- starts the loop. Checks today, since `J` is stuck on `h Top a`.
def Bot: Prop := (a: Prop) → a

def Top: Prop := Bot → Bot

def delta: Top := z => z Top z

def omega: ((a: Prop) → (b: Prop) → a = b) → Bot := h a => J (y e => y) delta (h Top a)

def bigOmega: ((a: Prop) → (b: Prop) → a = b) → Bot := h => delta (omega h)

theorem omegaUnfolds ∀ (h: (a: Prop) → (b: Prop) → a = b): bigOmega h = omega h Top (omega h) := byComputing
