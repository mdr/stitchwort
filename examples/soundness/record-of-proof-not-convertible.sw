-- expect-error: E-REFL
-- Lean Kernel Arena `eta-unit-like-proof-field` (docs/research/kernel.md
-- C24): with eta for records whose fields are all proofs, any two values
-- are equal, and a checker that did this halfway made conversion
-- non-transitive. The core has eta for functions only and no definitional
-- proof irrelevance, so two variables of `Box` differ. Neighbour: `box` in
-- accept/kernel-2026-neighbours.sw.
type Box = { h: 0 = 0 }

theorem bad (p q: Box): p = q := rfl
