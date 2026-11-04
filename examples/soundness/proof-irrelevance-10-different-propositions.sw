-- expect-error: E-TYPE-MISMATCH
-- The comparison skips proofs by position, so it relies on both sides having
-- one type (docs/core.md): boxes of proofs of different propositions are
-- never compared. Partner: `boxEq` in accept/proof-irrelevance.sw.

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

theorem t10 (a: Prop) (b: Prop) (p: a) (q: b): MkBox p = MkBox q := rfl
