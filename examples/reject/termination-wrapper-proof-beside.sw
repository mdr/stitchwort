-- expect-error: E-TERMINATION
-- Why every field counts towards "one field", proofs included, even though
-- the wrapper's part must be relevant data. A field of a proof is a part of
-- the value it was matched out of (the second clause, on `main` before the
-- wrapper rule). If `MkD xs q'` counted as a one-field wrapper because `q'`
-- is a proof, the first clause would be smaller too, and together they
-- loop: three first-clause calls take `[0, 0, 0]` to `[]` while burying
-- `MkD [0, 0, 0] q` in the proof, and the second clause digs it out again.
import Std (List, Nat, Unit)

type PBox (a: Type): Prop = | MkPBox (x: a)

type D: Type = | MkD (xs: List Nat) (q: PBox D)

theorem t: D → Unit
  | MkD [_, ..xs] q => t (MkD xs (MkPBox (MkD [0, 0, 0] q)))
  | MkD [] (MkPBox d) => t d
