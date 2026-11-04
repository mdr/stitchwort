-- expect-error: E-REFL
-- Inert positions stop at the definition's arity: `g`'s proof is an
-- argument of the function its case tree computes, which takes `J` on it.
-- Partner: `gComputes` in accept/proof-irrelevance.sw.
import Std (Bool, Nat)

def g (n: Nat): 0 = 0 → Bool :=
  match n with
    | Zero => h => J (y e => Bool) True h
    | Succ m => g m

theorem t24 (n: Nat) (h: 0 = 0): g n rfl = g n h := rfl
