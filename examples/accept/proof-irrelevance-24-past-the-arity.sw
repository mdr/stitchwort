-- `g`'s proof is an argument of the function its case tree computes, which
-- casts along it into data: the ends are `0` and `0`, so the cast is its base
-- (rule K), and the two proofs are equal by rule I (docs/core.md, "Proof
-- irrelevance") wherever they are compared.
-- Was soundness/proof-irrelevance-24-past-the-arity.sw, refused (E-REFL)
-- before rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).
import Std (Bool, Nat)

def g (n: Nat): 0 = 0 → Bool := match n with
  | Zero => h => J (y e => Bool) True h
  | Succ m => g m

theorem t24 ∀ (n: Nat) (h: 0 = 0): g n byComputing = g n h := byComputing
