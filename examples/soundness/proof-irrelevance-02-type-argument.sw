-- expect-error: E-REFL
-- A type argument of a definition is compared, though erased: only proofs
-- are skipped. Partner: `sameMod` in accept/proof-irrelevance.sw.
import Std (Bool, Nat)

def choose (t: Type) (n: Nat): Nat :=
  match n with
    | Zero => 0
    | Succ m => m

theorem t2 (n: Nat): choose Nat n = choose Bool n := rfl
