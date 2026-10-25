-- expect-error: E-PROP-ELIM
-- A record of type `Prop` is a proof, so its data fields can't be taken out:
-- that would let a proof decide data. Its proof fields can be
-- (`belowOf` in examples/accept/records.sw).

type Witness: Prop = { n: Nat, small: n ≤ 3 }

def witnessed (w: Witness): Nat := w.n
