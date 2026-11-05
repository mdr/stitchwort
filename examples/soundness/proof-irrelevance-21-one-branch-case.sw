-- expect-error: E-REFL
-- A `case` with a possible branch computes, so the proof it takes apart is
-- compared in stuck calls too. Partner: `absurdProofs` in
-- accept/proof-irrelevance.sw.
import Std (Nat)

type Tok: Prop =
  | MkTok

def tokNat (t: Tok) (k: Nat): Nat :=
  match t with
    | MkTok => k

theorem t21 (t: Tok) (t2: Tok): tokNat t 0 = tokNat t2 0 := rfl
