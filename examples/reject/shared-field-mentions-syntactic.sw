-- expect-error: E-UNKNOWN-FIELD
-- "Mentions" is syntactic: `label: Ignored len` mentions `len` although
-- `Ignored len` is `Nat` whatever `len` is, so `label` isn't shared.

def Ignored (n: Nat): Type := Nat

type G =
  | G1 (len: Nat) (label: Ignored len)
  | G2 (label: Ignored 0)

def gl (g: G): Nat := g.label
