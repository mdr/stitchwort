-- expect-error: E-REFL
-- Two proof variables are compared where they aren't at a proof position:
-- the masks are positional. Partner: `piViaBox` in accept/proof-irrelevance.sw.

theorem pi (a: Prop) (p: a) (q: a): p = q := rfl
