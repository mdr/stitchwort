-- A proof stored in a constructor field: the two sides unfold to `p` and `q`,
-- which are equal by rule I (docs/core.md, "Proof irrelevance"); unfolded
-- or not, both sides are proofs.
-- Was soundness/proof-irrelevance-23-stored-in-a-field.sw, refused (E-REFL)
-- before rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).
import Std (Nat)

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

def keep (d: Nat) (ok: d ≠ 0): Box (d ≠ 0) := MkBox ok

theorem t23 ∀ (d: Nat) (p q: d ≠ 0): Box.unbox (keep d p) = Box.unbox (keep d q) := byComputing
