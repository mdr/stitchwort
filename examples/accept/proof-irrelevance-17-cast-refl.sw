-- `cast` takes `J` on its proof, so the proof isn't inert, and the glued
-- shortcut finds `byComputing` and `h` different; but both unfoldings are `x`:
-- along `h: a = a` the cast's ends are equal, so it is its base (rule K,
-- docs/core.md, "The equality rule"). Was
-- soundness/proof-irrelevance-17-cast-refl.sw, refused (E-REFL) before rule K.
-- Partner: `castRflComputes` in accept/proof-irrelevance.sw.

def cast (a b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castRefl ∀ (a: Type) (h: a = a) (x: a): cast a a byComputing x = cast a a h x := byComputing
