-- Two `case`s on proofs of a proposition with one constructor, into data,
-- each take their branch whatever the proof (rule S, docs/core.md, "The
-- equality rule"), so `tokA t` and `tokB t2` are both `0`. Was
-- soundness/proof-irrelevance-27-one-branch-trees.sw, refused (E-REFL) while
-- a `case` with a possible branch compared its scrutinees. Partner:
-- `absurdTransitive` in accept/proof-irrelevance.sw.
import Std (Nat)

type Tok: Prop = | MkTok

def tokA (t: Tok): Nat := match t with | MkTok => 0

def tokB (t: Tok): Nat := match t with | MkTok => 0

theorem t27 ∀ (t t2: Tok): tokA t = tokB t2 := byComputing
