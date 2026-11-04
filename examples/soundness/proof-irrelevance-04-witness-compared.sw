-- expect-error: E-REFL
-- A data field inside a proof is still compared: irrelevance is for proof
-- positions, not for every value of a proposition. (Matching the witness out
-- as data is E-PROP-ELIM: exists-witness.sw.) Partner: `sameWitness` in
-- accept/proof-irrelevance.sw.
import Std (Nat)

type Exists (p: Nat → Prop): Prop =
  | MkEx (x: Nat) (h: p x)

def one: Exists (n => n = n) := MkEx 1 rfl
def two: Exists (n => n = n) := MkEx 2 rfl

theorem t4: one = two := rfl
