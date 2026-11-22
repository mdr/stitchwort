-- A proof stuck past its own case tree is kept as the lemma's call
-- (SW-4642): `flipped n p` stays that, though it unfolds to a `J` stuck on
-- `p`. A transport by it still equals one by that unfolding written out,
-- both when computed (`byComputing`) and when unified (a hypothesis
-- against the goal): the call is unfolded, and the `J` after it applied,
-- to compare them.
type Tag (n: Nat) = | MkTag (k: Nat)

theorem flipped ∀ (n: Nat) (p: n = 3): 3 = n := J (m _ => m = n) byComputing p

theorem computed ∀ (n: Nat)
    (p: n = 3) (x: Tag 3):
    J (m _ => Tag m) x (flipped n p) = J (m _ => Tag m) x (J (m _ => m = n) byComputing p) :=
  byComputing

theorem unified ∀ (n: Nat)
    (p: n = 3)
    (x: Tag 3) (q: Tag n → Prop) (h: q (J (m _ => Tag m) x (flipped n p))):
    q (J (m _ => Tag m) x (J (m _ => m = n) byComputing p)) :=
  h
