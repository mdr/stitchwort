-- expect-error: E-REFL
-- A type field is erased at runtime but compared: only proofs are skipped.
-- Accepted partner: accept/proof-irrelevance.sw (`charProof`).
import Std (Bool, Nat)

type TBox: Type 1 =
  | MkTBox (t: Type)

theorem t1: MkTBox Nat = MkTBox Bool := rfl
