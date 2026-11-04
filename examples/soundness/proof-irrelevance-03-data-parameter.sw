-- expect-error: E-REFL
-- A data type's parameter that is data is compared; only proof parameters
-- are skipped. Partner: `proofParameter` in accept/proof-irrelevance.sw.
import Std (List, Nat)

type Sorted (xs: List Nat): Prop =
  | MkSorted

theorem t3: Sorted [1, 2] = Sorted [2, 1] := rfl
