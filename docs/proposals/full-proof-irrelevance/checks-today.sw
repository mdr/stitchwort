-- Probe for docs/proposals/full-proof-irrelevance.md: what already checks today,
-- and with every theorem sealed (`STITCHWORT_SEAL_THEOREMS=1
-- STITCHWORT_SEAL_EXCEPT=Std.Eq.trans,Std.Eq.flipped`). Under E2 each
-- `Prop.irrel …` below could be `byComputing`.
import Std (Bool, Eq, Nat)

type Box (a: Prop): Type = | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

-- Every two proofs of one proposition are equal: a theorem since D1′.
theorem Prop.irrel ∀ (a: Prop) (p q: a): p = q :=
  J (y e => p = Box.unbox y) byComputing ((byComputing: MkBox p = MkBox q))

-- Std's Hedberg lemmas (`symThenSelf`, `fromCanon`, `uniqueEq` in
-- std/core/Decidable.sw) say this for equations at a decidable type. Their
-- statements follow from `Prop.irrel` with no decision procedure and no
-- look inside `Eq.trans` or `Eq.flipped`.
theorem symThenSelf ∀ [a: Type] [x y: a] (q: x = y): byComputing = Eq.trans q.flipped q :=
  Prop.irrel (y = y) byComputing (Eq.trans q.flipped q)

theorem uniqueEq ∀ [a: Type] (x y: a) (p q: x = y): p = q := Prop.irrel (x = y) p q

theorem uniqueBool ∀ (x y: Bool) (p q: x = y): p = q := Prop.irrel (x = y) p q

-- Checks today for an unknown `n` (the proof field is skipped while `depth` is
-- stuck), though the instance at `n = 1` is refused (`atOne` in e2-only.sw):
-- the gap of proof-irrelevance.md section 5.7.
def depth (b: Box (0 = 0)) (n: Nat): Nat := match n with
  | Zero => 0
  | Succ m =>
    match b with
      | MkBox h => J (y e => Nat) m h

theorem underStuck ∀ (n: Nat) (p q: 0 = 0): depth (MkBox p) n = depth (MkBox q) n := byComputing
