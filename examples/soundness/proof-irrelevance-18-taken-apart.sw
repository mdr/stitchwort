-- expect-error: E-REFL
-- `tokNat` takes its proof apart, so the proof isn't inert: the shortcut
-- compares `t` and `MkTok`, as unfolding does (one side computes). Partner:
-- `tokNatComputes` in accept/self-referential-prop.sw.
import Std (Nat)

type Tok: Prop =
  | MkTok

def tokNat (t: Tok) (k: Nat): Nat :=
  match t with
    | MkTok => k

theorem t18 (t: Tok): tokNat t 0 = tokNat MkTok 0 := rfl
