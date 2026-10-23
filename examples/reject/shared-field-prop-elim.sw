-- expect-error: E-UNKNOWN-FIELD
-- `witness`'s type mentions `p`, which isn't shared: `Claims` is a
-- proposition, and `p` is data, which can't be taken out of a proof.

type Claims: Prop =
  | P (p: Prop) (witness: p)
  | Q (p: Prop) (witness: p)

def w (c: Claims): Bool := c.witness
