-- `tokNat` takes its proof apart, so the proof isn't inert and the shortcut
-- finds `t` and `MkTok` different; but both calls unfold to `0`: a match into
-- data on a proof of a proposition with one constructor takes its branch
-- whatever the proof (rule S, docs/core.md, "The equality rule"). Was
-- soundness/proof-irrelevance-18-taken-apart.sw, refused (E-REFL) before rule
-- S. Partner: `tokNatComputes` in accept/self-referential-prop.sw.
import Std (Nat)

type Tok: Prop = | MkTok

def tokNat (t: Tok) (k: Nat): Nat := match t with | MkTok => k

theorem t18 ∀ (t: Tok): tokNat t 0 = tokNat MkTok 0 := byComputing
