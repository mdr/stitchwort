-- expect-error: E-REFL
-- `cast` takes `J` on its proof, so the proof isn't inert, and the glued
-- shortcut compares it: `rfl` and `h` differ, as do the unfoldings (`x`
-- and a stuck `J`). Partner: `castRflComputes` in accept/proof-irrelevance.sw.

def cast (a: Type) (b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castRefl (a: Type) (h: a = a) (x: a): cast a a rfl x = cast a a h x := rfl
