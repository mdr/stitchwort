-- A proposition whose field holds a proof of itself may be declared and
-- matched to produce other proofs, structural recursion included; only
-- matching it into data is refused (soundness/self-referential-prop-elim.sw).
-- A non-recursive proposition with one constructor still produces data.
import Std (Nat, Void)

type Loop: Prop =
  | MkLoop (next: Loop)

def Loop.inv: Loop → Loop
  | MkLoop n => n

def Loop.empty: Loop → Void
  | MkLoop n => Loop.empty n

type Tok: Prop =
  | MkTok

def tokNat (t: Tok) (k: Nat): Nat := match t with
  | MkTok => k

theorem tokNatComputes ∀ (k: Nat): tokNat MkTok k = k := rfl
