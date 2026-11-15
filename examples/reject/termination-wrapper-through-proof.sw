-- expect-error: E-TERMINATION
-- The wrapper's one field is data, but `r` is reached from it through the
-- proof field `pf` of the record `R`: a part of a proof, so not a strict
-- part for the wrapper rule. Every step from the matched field to the part
-- must be a field of relevant data.
import Std (Nat, Void)

type PBox (a: Type): Prop = | MkPBox (x: a)

type R = { tag: Nat, pf: PBox R }

type W: Type = | MkW (r: R)

def g: W → Void
  | MkW { tag = _, pf = MkPBox r } => g (MkW r)
