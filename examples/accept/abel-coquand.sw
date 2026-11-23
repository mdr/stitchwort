-- The Abel-Coquand program: under the hypothesis `h` that every two
-- propositions are equal, `bigOmega h` would compute to itself for ever if a
-- cast along any proof of `Top = Top` computed. Every term here is a proof
-- (of `Bot` or `Top`), so a checker that never computes inside a proof never
-- starts the loop; `J` is stuck on `h Top a`. It must keep checking, whatever
-- the proof-irrelevance rules become (docs/proposals/proof-irrelevance.md
-- section 5.2, docs/proposals/full-proof-irrelevance.md section 5.3).
def Bot: Prop := ∀ (a: Prop) => a

def Top: Prop := Bot → Bot

def delta: Top := z => z Top z

def omega: (∀ (a b: Prop) => a = b) → Bot := h a => J (y e => y) delta (h Top a)

def bigOmega: (∀ (a b: Prop) => a = b) → Bot := h => delta (omega h)

theorem omegaUnfolds ∀ (h: ∀ (a b: Prop) => a = b): bigOmega h = omega h Top (omega h) := byComputing
