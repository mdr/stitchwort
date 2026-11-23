-- A `case` into data on a proof of a proposition with one constructor takes
-- its branch whatever the proof (rule S, docs/core.md, "The equality rule"):
-- `tokNat t 0` and `tokNat t2 0` are both `0`. Was
-- soundness/proof-irrelevance-21-one-branch-case.sw, refused (E-REFL) while
-- such a `case` computed on a constructor only. Partner: `absurdProofs` in
-- accept/proof-irrelevance.sw.
import Std (Nat)

type Tok: Prop = | MkTok

def tokNat (t: Tok) (k: Nat): Nat := match t with | MkTok => k

theorem t21 ∀ (t t2: Tok): tokNat t 0 = tokNat t2 0 := byComputing
