-- `one` and `two` are proofs of one proposition (`Exists` is a `Prop`), so
-- they are equal unlooked at, whatever witness each holds: rule I
-- (docs/core.md, "Proof irrelevance"). The witness can't be read back out as
-- data (E-PROP-ELIM: soundness/exists-witness.sw), so nothing tells them apart.
-- Was soundness/proof-irrelevance-04-witness-compared.sw, refused (E-REFL)
-- before rule I (stage 5 of docs/proposals/full-proof-irrelevance.md).
import Std (Nat)

type Exists (p: Nat → Prop): Prop = | MkEx (x: Nat) (h: p x)

def one: Exists (n => n = n) := MkEx 1 byComputing
def two: Exists (n => n = n) := MkEx 2 byComputing

theorem t4: one = two := byComputing
