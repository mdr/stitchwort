-- `grpA` takes `h` apart with `J`, into data, and `grpB` passes it on; the
-- results are the same for `p` and `q` because the cast's ends are equal
-- (rule K) and the proofs are compared by rule I (docs/core.md, "Proof
-- irrelevance"), with no analysis of what a group does with `h`.
-- Was soundness/proof-irrelevance-22-through-the-group.sw, refused (E-REFL)
-- before rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).
import Std (Nat)

def grpA (n: Nat) (h: 0 = 0): Nat := match n with
  | Zero => J (y e => Nat) 0 h
  | Succ m => grpB m h

def grpB (n: Nat) (h: 0 = 0): Nat := match n with
  | Zero => 1
  | Succ m => grpA m h

theorem t22 ∀ (n: Nat) (p q: 0 = 0): grpB n p = grpB n q := byComputing
